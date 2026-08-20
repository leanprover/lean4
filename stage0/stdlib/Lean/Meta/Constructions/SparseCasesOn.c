// Lean compiler output
// Module: Lean.Meta.Constructions.SparseCasesOn
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.Constructions.CtorIdx import Lean.Meta.HasNotBit import Lean.Meta.Transform
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Environment_hasExposedBody(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkHasNotBit(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
static const lean_array_object l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SparseCasesOn"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 142, 211, 52, 27, 176, 89, 6)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(93, 38, 184, 128, 76, 32, 215, 209)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 79, 91, 86, 222, 171, 161, 209)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 83, 47, 52, 170, 238, 223, 102)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sparseCasesOnInfoExt"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 231, 162, 79, 58, 254, 239, 178)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 140, 41, 106, 106, 114, 66, 206)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3_value;
static const lean_array_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "mkSparseCasesOn: unexpected number of parameters in type of `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "mkSparseCasesOn: constructor "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " is not a constructor of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Meta.Constructions.SparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__0 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__0_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.mkSparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__2;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "mkSparseCasesOn: unexpected number of universe parameters in `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__3 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__3_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__4;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__5;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "_sparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__6 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__6_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__6_value),LEAN_SCALAR_PTR_LITERAL(111, 99, 43, 146, 60, 255, 155, 135)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__7 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__7_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "mkSparseCasesOn: requested casesOn combinator is not sparse"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__8 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__8_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(lean_object* v_xs_1_, lean_object* v_ys_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_x_3_);
return v_isZero_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_3_, v_one_6_);
lean_dec(v_x_3_);
v___x_8_ = lean_array_fget_borrowed(v_xs_1_, v_n_7_);
v___x_9_ = lean_array_fget_borrowed(v_ys_2_, v_n_7_);
v___x_10_ = lean_name_eq(v___x_8_, v___x_9_);
if (v___x_10_ == 0)
{
lean_dec(v_n_7_);
return v___x_10_;
}
else
{
v_x_3_ = v_n_7_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg___boxed(lean_object* v_xs_12_, lean_object* v_ys_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_12_, v_ys_13_, v_x_14_);
lean_dec_ref(v_ys_13_);
lean_dec_ref(v_xs_12_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_indName_19_; lean_object* v_ctors_20_; uint8_t v_isPrivate_21_; lean_object* v_indName_22_; lean_object* v_ctors_23_; uint8_t v_isPrivate_24_; uint8_t v___x_25_; 
v_indName_19_ = lean_ctor_get(v_x_17_, 0);
v_ctors_20_ = lean_ctor_get(v_x_17_, 1);
v_isPrivate_21_ = lean_ctor_get_uint8(v_x_17_, sizeof(void*)*2);
v_indName_22_ = lean_ctor_get(v_x_18_, 0);
v_ctors_23_ = lean_ctor_get(v_x_18_, 1);
v_isPrivate_24_ = lean_ctor_get_uint8(v_x_18_, sizeof(void*)*2);
v___x_25_ = lean_name_eq(v_indName_19_, v_indName_22_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_26_ = lean_array_get_size(v_ctors_20_);
v___x_27_ = lean_array_get_size(v_ctors_23_);
v___x_28_ = lean_nat_dec_eq(v___x_26_, v___x_27_);
if (v___x_28_ == 0)
{
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_ctors_20_, v_ctors_23_, v___x_26_);
if (v___x_29_ == 0)
{
return v___x_29_;
}
else
{
if (v_isPrivate_24_ == 0)
{
if (v_isPrivate_21_ == 0)
{
return v___x_29_;
}
else
{
return v_isPrivate_24_;
}
}
else
{
return v_isPrivate_21_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_30_, v_x_31_);
lean_dec_ref(v_x_31_);
lean_dec_ref(v_x_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(lean_object* v_xs_34_, lean_object* v_ys_35_, lean_object* v_hsz_36_, lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_34_, v_ys_35_, v_x_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___boxed(lean_object* v_xs_40_, lean_object* v_ys_41_, lean_object* v_hsz_42_, lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(v_xs_40_, v_ys_41_, v_hsz_42_, v_x_43_, v_x_44_);
lean_dec_ref(v_ys_41_);
lean_dec_ref(v_xs_40_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(lean_object* v_as_49_, size_t v_i_50_, size_t v_stop_51_, uint64_t v_b_52_){
_start:
{
uint64_t v___y_54_; uint8_t v___x_59_; 
v___x_59_ = lean_usize_dec_eq(v_i_50_, v_stop_51_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
v___x_60_ = lean_array_uget_borrowed(v_as_49_, v_i_50_);
if (lean_obj_tag(v___x_60_) == 0)
{
uint64_t v___x_61_; 
v___x_61_ = 1723ULL;
v___y_54_ = v___x_61_;
goto v___jp_53_;
}
else
{
uint64_t v_hash_62_; 
v_hash_62_ = lean_ctor_get_uint64(v___x_60_, sizeof(void*)*2);
v___y_54_ = v_hash_62_;
goto v___jp_53_;
}
}
else
{
return v_b_52_;
}
v___jp_53_:
{
uint64_t v___x_55_; size_t v___x_56_; size_t v___x_57_; 
v___x_55_ = lean_uint64_mix_hash(v_b_52_, v___y_54_);
v___x_56_ = ((size_t)1ULL);
v___x_57_ = lean_usize_add(v_i_50_, v___x_56_);
v_i_50_ = v___x_57_;
v_b_52_ = v___x_55_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(lean_object* v_as_63_, lean_object* v_i_64_, lean_object* v_stop_65_, lean_object* v_b_66_){
_start:
{
size_t v_i_boxed_67_; size_t v_stop_boxed_68_; uint64_t v_b_boxed_69_; uint64_t v_res_70_; lean_object* v_r_71_; 
v_i_boxed_67_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_stop_boxed_68_ = lean_unbox_usize(v_stop_65_);
lean_dec(v_stop_65_);
v_b_boxed_69_ = lean_unbox_uint64(v_b_66_);
lean_dec_ref(v_b_66_);
v_res_70_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_as_63_, v_i_boxed_67_, v_stop_boxed_68_, v_b_boxed_69_);
lean_dec_ref(v_as_63_);
v_r_71_ = lean_box_uint64(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(lean_object* v_x_72_){
_start:
{
lean_object* v_indName_73_; lean_object* v_ctors_74_; uint8_t v_isPrivate_75_; uint64_t v___y_77_; uint64_t v___y_78_; uint64_t v___x_84_; uint64_t v___y_86_; 
v_indName_73_ = lean_ctor_get(v_x_72_, 0);
v_ctors_74_ = lean_ctor_get(v_x_72_, 1);
v_isPrivate_75_ = lean_ctor_get_uint8(v_x_72_, sizeof(void*)*2);
v___x_84_ = 0ULL;
if (lean_obj_tag(v_indName_73_) == 0)
{
uint64_t v___x_95_; 
v___x_95_ = 1723ULL;
v___y_86_ = v___x_95_;
goto v___jp_85_;
}
else
{
uint64_t v_hash_96_; 
v_hash_96_ = lean_ctor_get_uint64(v_indName_73_, sizeof(void*)*2);
v___y_86_ = v_hash_96_;
goto v___jp_85_;
}
v___jp_76_:
{
uint64_t v___x_79_; 
v___x_79_ = lean_uint64_mix_hash(v___y_77_, v___y_78_);
if (v_isPrivate_75_ == 0)
{
uint64_t v___x_80_; uint64_t v___x_81_; 
v___x_80_ = 13ULL;
v___x_81_ = lean_uint64_mix_hash(v___x_79_, v___x_80_);
return v___x_81_;
}
else
{
uint64_t v___x_82_; uint64_t v___x_83_; 
v___x_82_ = 11ULL;
v___x_83_ = lean_uint64_mix_hash(v___x_79_, v___x_82_);
return v___x_83_;
}
}
v___jp_85_:
{
uint64_t v___x_87_; uint64_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_87_ = lean_uint64_mix_hash(v___x_84_, v___y_86_);
v___x_88_ = 7ULL;
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_array_get_size(v_ctors_74_);
v___x_91_ = lean_nat_dec_lt(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
v___y_77_ = v___x_87_;
v___y_78_ = v___x_88_;
goto v___jp_76_;
}
else
{
size_t v___x_92_; size_t v___x_93_; uint64_t v___x_94_; 
v___x_92_ = ((size_t)0ULL);
v___x_93_ = lean_usize_of_nat(v___x_90_);
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_ctors_74_, v___x_92_, v___x_93_, v___x_88_);
v___y_77_ = v___x_87_;
v___y_78_ = v___x_94_;
goto v___jp_76_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(lean_object* v_x_97_){
_start:
{
uint64_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_97_);
lean_dec_ref(v_x_97_);
v_r_99_ = lean_box_uint64(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(lean_object* v___x_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed(lean_object* v___x_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(v___x_105_);
return v_res_107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_111_; lean_object* v___f_112_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_);
v___f_112_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_112_, 0, v___x_111_);
return v___f_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___f_114_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_);
v___x_115_ = lean_box(0);
v___x_116_ = lean_box(1);
v___x_117_ = l_Lean_registerEnvExtension___redArg(v___f_114_, v___x_115_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed(lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_();
return v_res_119_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object* v_env_128_, lean_object* v_n_129_, lean_object* v_x_130_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_Environment_hasExposedBody(v_env_128_, v_n_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object* v_env_132_, lean_object* v_n_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(v_env_132_, v_n_133_, v_x_134_);
lean_dec_ref(v_x_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_137_, lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_k_139_; lean_object* v_v_140_; lean_object* v_l_141_; lean_object* v_r_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_k_139_ = lean_ctor_get(v_x_138_, 1);
v_v_140_ = lean_ctor_get(v_x_138_, 2);
v_l_141_ = lean_ctor_get(v_x_138_, 3);
v_r_142_ = lean_ctor_get(v_x_138_, 4);
v___x_143_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_137_, v_l_141_);
lean_inc(v_v_140_);
lean_inc(v_k_139_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v_k_139_);
lean_ctor_set(v___x_144_, 1, v_v_140_);
v___x_145_ = lean_array_push(v___x_143_, v___x_144_);
v_init_137_ = v___x_145_;
v_x_138_ = v_r_142_;
goto _start;
}
else
{
return v_init_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_147_, lean_object* v_x_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_147_, v_x_148_);
lean_dec(v_x_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object* v_env_152_, lean_object* v_s_153_){
_start:
{
lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v_all_156_; lean_object* v___x_157_; lean_object* v_exported_158_; lean_object* v___x_159_; 
v___f_154_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_154_, 0, v_env_152_);
v___x_155_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v_all_156_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v___x_155_, v_s_153_);
v___x_157_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_154_, v_s_153_);
v_exported_158_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v___x_155_, v___x_157_);
lean_dec(v___x_157_);
lean_inc_ref(v_exported_158_);
v___x_159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_159_, 0, v_exported_158_);
lean_ctor_set(v___x_159_, 1, v_exported_158_);
lean_ctor_set(v___x_159_, 2, v_all_156_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___f_197_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_198_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_200_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_198_, v___x_199_, v___f_197_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(lean_object* v_init_203_, lean_object* v_t_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_203_, v_t_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_206_, lean_object* v_t_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(v_init_206_, v_t_207_);
lean_dec(v_t_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(lean_object* v_kind_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v_auxDeclNGen_213_; lean_object* v___x_214_; lean_object* v_env_215_; lean_object* v___x_216_; lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_219_; lean_object* v_env_220_; lean_object* v_nextMacroScope_221_; lean_object* v_ngen_222_; lean_object* v_traceState_223_; lean_object* v_cache_224_; lean_object* v_messages_225_; lean_object* v_infoState_226_; lean_object* v_snapshotTasks_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_236_; 
v___x_212_ = lean_st_ref_get(v___y_210_);
v_auxDeclNGen_213_ = lean_ctor_get(v___x_212_, 3);
lean_inc_ref(v_auxDeclNGen_213_);
lean_dec(v___x_212_);
v___x_214_ = lean_st_ref_get(v___y_210_);
v_env_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc_ref(v_env_215_);
lean_dec(v___x_214_);
v___x_216_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_215_, v_auxDeclNGen_213_, v_kind_209_);
v_fst_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_fst_217_);
v_snd_218_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_snd_218_);
lean_dec_ref(v___x_216_);
v___x_219_ = lean_st_ref_take(v___y_210_);
v_env_220_ = lean_ctor_get(v___x_219_, 0);
v_nextMacroScope_221_ = lean_ctor_get(v___x_219_, 1);
v_ngen_222_ = lean_ctor_get(v___x_219_, 2);
v_traceState_223_ = lean_ctor_get(v___x_219_, 4);
v_cache_224_ = lean_ctor_get(v___x_219_, 5);
v_messages_225_ = lean_ctor_get(v___x_219_, 6);
v_infoState_226_ = lean_ctor_get(v___x_219_, 7);
v_snapshotTasks_227_ = lean_ctor_get(v___x_219_, 8);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v___x_219_, 3);
lean_dec(v_unused_237_);
v___x_229_ = v___x_219_;
v_isShared_230_ = v_isSharedCheck_236_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_snapshotTasks_227_);
lean_inc(v_infoState_226_);
lean_inc(v_messages_225_);
lean_inc(v_cache_224_);
lean_inc(v_traceState_223_);
lean_inc(v_ngen_222_);
lean_inc(v_nextMacroScope_221_);
lean_inc(v_env_220_);
lean_dec(v___x_219_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_236_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 3, v_snd_218_);
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_env_220_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_nextMacroScope_221_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_ngen_222_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_snd_218_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_traceState_223_);
lean_ctor_set(v_reuseFailAlloc_235_, 5, v_cache_224_);
lean_ctor_set(v_reuseFailAlloc_235_, 6, v_messages_225_);
lean_ctor_set(v_reuseFailAlloc_235_, 7, v_infoState_226_);
lean_ctor_set(v_reuseFailAlloc_235_, 8, v_snapshotTasks_227_);
v___x_232_ = v_reuseFailAlloc_235_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_st_ref_put(v___y_210_, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_fst_217_);
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(lean_object* v_kind_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_238_, v___y_239_);
lean_dec(v___y_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(lean_object* v_kind_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_242_, v___y_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(lean_object* v_kind_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(v_kind_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0(lean_object* v_k_256_, lean_object* v_b_257_, lean_object* v_c_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_264_; 
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
lean_inc(v___y_260_);
lean_inc_ref(v___y_259_);
v___x_264_ = lean_apply_7(v_k_256_, v_b_257_, v_c_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, lean_box(0));
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0___boxed(lean_object* v_k_265_, lean_object* v_b_266_, lean_object* v_c_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0(v_k_265_, v_b_266_, v_c_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(lean_object* v_type_274_, lean_object* v_k_275_, uint8_t v_cleanupAnnotations_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___f_282_; uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___f_282_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_282_, 0, v_k_275_);
v___x_283_ = 0;
v___x_284_ = lean_box(0);
v___x_285_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_283_, v___x_284_, v_type_274_, v___f_282_, v_cleanupAnnotations_276_, v___x_283_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
v_a_294_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_285_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_285_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___boxed(lean_object* v_type_302_, lean_object* v_k_303_, lean_object* v_cleanupAnnotations_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_310_; lean_object* v_res_311_; 
v_cleanupAnnotations_boxed_310_ = lean_unbox(v_cleanupAnnotations_304_);
v_res_311_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v_type_302_, v_k_303_, v_cleanupAnnotations_boxed_310_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11(lean_object* v_00_u03b1_312_, lean_object* v_type_313_, lean_object* v_k_314_, uint8_t v_cleanupAnnotations_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v_type_313_, v_k_314_, v_cleanupAnnotations_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(lean_object* v_00_u03b1_322_, lean_object* v_type_323_, lean_object* v_k_324_, lean_object* v_cleanupAnnotations_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_331_; lean_object* v_res_332_; 
v_cleanupAnnotations_boxed_331_ = lean_unbox(v_cleanupAnnotations_325_);
v_res_332_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11(v_00_u03b1_322_, v_type_323_, v_k_324_, v_cleanupAnnotations_boxed_331_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(lean_object* v_name_333_, lean_object* v_levelParams_334_, lean_object* v_type_335_, lean_object* v_value_336_, lean_object* v_hints_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; uint8_t v___y_342_; uint8_t v___y_349_; lean_object* v_env_352_; uint8_t v___x_353_; 
v___x_340_ = lean_st_ref_get(v___y_338_);
v_env_352_ = lean_ctor_get(v___x_340_, 0);
lean_inc_ref_n(v_env_352_, 2);
lean_dec(v___x_340_);
v___x_353_ = l_Lean_Environment_hasUnsafe(v_env_352_, v_type_335_);
if (v___x_353_ == 0)
{
uint8_t v___x_354_; 
v___x_354_ = l_Lean_Environment_hasUnsafe(v_env_352_, v_value_336_);
v___y_349_ = v___x_354_;
goto v___jp_348_;
}
else
{
lean_dec_ref(v_env_352_);
v___y_349_ = v___x_353_;
goto v___jp_348_;
}
v___jp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_inc(v_name_333_);
v___x_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_343_, 0, v_name_333_);
lean_ctor_set(v___x_343_, 1, v_levelParams_334_);
lean_ctor_set(v___x_343_, 2, v_type_335_);
v___x_344_ = lean_box(0);
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v_name_333_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_346_, 0, v___x_343_);
lean_ctor_set(v___x_346_, 1, v_value_336_);
lean_ctor_set(v___x_346_, 2, v_hints_337_);
lean_ctor_set(v___x_346_, 3, v___x_345_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*4, v___y_342_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
v___jp_348_:
{
if (v___y_349_ == 0)
{
uint8_t v___x_350_; 
v___x_350_ = 1;
v___y_342_ = v___x_350_;
goto v___jp_341_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = 0;
v___y_342_ = v___x_351_;
goto v___jp_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(lean_object* v_name_355_, lean_object* v_levelParams_356_, lean_object* v_type_357_, lean_object* v_value_358_, lean_object* v_hints_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_name_355_, v_levelParams_356_, v_type_357_, v_value_358_, v_hints_359_, v___y_360_);
lean_dec(v___y_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_object* v_name_363_, lean_object* v_levelParams_364_, lean_object* v_type_365_, lean_object* v_value_366_, lean_object* v_hints_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_name_363_, v_levelParams_364_, v_type_365_, v_value_366_, v_hints_367_, v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(lean_object* v_name_374_, lean_object* v_levelParams_375_, lean_object* v_type_376_, lean_object* v_value_377_, lean_object* v_hints_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14(v_name_374_, v_levelParams_375_, v_type_376_, v_value_377_, v_hints_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___f_392_; lean_object* v___x_16843__overap_393_; lean_object* v___x_394_; 
v___f_392_ = ((lean_object*)(l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0));
v___x_16843__overap_393_ = lean_panic_fn_borrowed(v___f_392_, v_msg_386_);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
v___x_394_ = lean_apply_5(v___x_16843__overap_393_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, lean_box(0));
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(lean_object* v_msg_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(v_msg_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
lean_object* v_ks_406_; lean_object* v_vs_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_431_; 
v_ks_406_ = lean_ctor_get(v_x_402_, 0);
v_vs_407_ = lean_ctor_get(v_x_402_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_402_);
if (v_isSharedCheck_431_ == 0)
{
v___x_409_ = v_x_402_;
v_isShared_410_ = v_isSharedCheck_431_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_vs_407_);
lean_inc(v_ks_406_);
lean_dec(v_x_402_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_431_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_array_get_size(v_ks_406_);
v___x_412_ = lean_nat_dec_lt(v_x_403_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
lean_dec(v_x_403_);
v___x_413_ = lean_array_push(v_ks_406_, v_x_404_);
v___x_414_ = lean_array_push(v_vs_407_, v_x_405_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_414_);
lean_ctor_set(v___x_409_, 0, v___x_413_);
v___x_416_ = v___x_409_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
lean_object* v_k_x27_418_; uint8_t v___x_419_; 
v_k_x27_418_ = lean_array_fget_borrowed(v_ks_406_, v_x_403_);
v___x_419_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_404_, v_k_x27_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_421_; 
if (v_isShared_410_ == 0)
{
v___x_421_ = v___x_409_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_ks_406_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_vs_407_);
v___x_421_ = v_reuseFailAlloc_425_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_x_403_, v___x_422_);
lean_dec(v_x_403_);
v_x_402_ = v___x_421_;
v_x_403_ = v___x_423_;
goto _start;
}
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_426_ = lean_array_fset(v_ks_406_, v_x_403_, v_x_404_);
v___x_427_ = lean_array_fset(v_vs_407_, v_x_403_, v_x_405_);
lean_dec(v_x_403_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_427_);
lean_ctor_set(v___x_409_, 0, v___x_426_);
v___x_429_ = v___x_409_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(lean_object* v_n_432_, lean_object* v_k_433_, lean_object* v_v_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(v_n_432_, v___x_435_, v_k_433_, v_v_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(lean_object* v_x_438_, size_t v_x_439_, size_t v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
lean_object* v_es_443_; size_t v___x_444_; size_t v___x_445_; lean_object* v_j_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_es_443_ = lean_ctor_get(v_x_438_, 0);
v___x_444_ = ((size_t)31ULL);
v___x_445_ = lean_usize_land(v_x_439_, v___x_444_);
v_j_446_ = lean_usize_to_nat(v___x_445_);
v___x_447_ = lean_array_get_size(v_es_443_);
v___x_448_ = lean_nat_dec_lt(v_j_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_dec(v_j_446_);
lean_dec(v_x_442_);
lean_dec_ref(v_x_441_);
return v_x_438_;
}
else
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_487_; 
lean_inc_ref(v_es_443_);
v_isSharedCheck_487_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v_x_438_, 0);
lean_dec(v_unused_488_);
v___x_450_ = v_x_438_;
v_isShared_451_ = v_isSharedCheck_487_;
goto v_resetjp_449_;
}
else
{
lean_dec(v_x_438_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_487_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_v_452_; lean_object* v___x_453_; lean_object* v_xs_x27_454_; lean_object* v___y_456_; 
v_v_452_ = lean_array_fget(v_es_443_, v_j_446_);
v___x_453_ = lean_box(0);
v_xs_x27_454_ = lean_array_fset(v_es_443_, v_j_446_, v___x_453_);
switch(lean_obj_tag(v_v_452_))
{
case 0:
{
lean_object* v_key_461_; lean_object* v_val_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_472_; 
v_key_461_ = lean_ctor_get(v_v_452_, 0);
v_val_462_ = lean_ctor_get(v_v_452_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_v_452_);
if (v_isSharedCheck_472_ == 0)
{
v___x_464_ = v_v_452_;
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_val_462_);
lean_inc(v_key_461_);
lean_dec(v_v_452_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; 
v___x_466_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_441_, v_key_461_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_del_object(v___x_464_);
v___x_467_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_461_, v_val_462_, v_x_441_, v_x_442_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
v___y_456_ = v___x_468_;
goto v___jp_455_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v_val_462_);
lean_dec(v_key_461_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v_x_442_);
lean_ctor_set(v___x_464_, 0, v_x_441_);
v___x_470_ = v___x_464_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_x_441_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_x_442_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
v___y_456_ = v___x_470_;
goto v___jp_455_;
}
}
}
}
case 1:
{
lean_object* v_node_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_485_; 
v_node_473_ = lean_ctor_get(v_v_452_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v_v_452_);
if (v_isSharedCheck_485_ == 0)
{
v___x_475_ = v_v_452_;
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_node_473_);
lean_dec(v_v_452_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_477_ = ((size_t)5ULL);
v___x_478_ = lean_usize_shift_right(v_x_439_, v___x_477_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_add(v_x_440_, v___x_479_);
v___x_481_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_node_473_, v___x_478_, v___x_480_, v_x_441_, v_x_442_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_481_);
v___x_483_ = v___x_475_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
v___y_456_ = v___x_483_;
goto v___jp_455_;
}
}
}
default: 
{
lean_object* v___x_486_; 
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_x_441_);
lean_ctor_set(v___x_486_, 1, v_x_442_);
v___y_456_ = v___x_486_;
goto v___jp_455_;
}
}
v___jp_455_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = lean_array_fset(v_xs_x27_454_, v_j_446_, v___y_456_);
lean_dec(v_j_446_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_457_);
v___x_459_ = v___x_450_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
else
{
lean_object* v_ks_489_; lean_object* v_vs_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_508_; 
v_ks_489_ = lean_ctor_get(v_x_438_, 0);
v_vs_490_ = lean_ctor_get(v_x_438_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_508_ == 0)
{
v___x_492_ = v_x_438_;
v_isShared_493_ = v_isSharedCheck_508_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_vs_490_);
lean_inc(v_ks_489_);
lean_dec(v_x_438_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_508_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_ks_489_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_vs_490_);
v___x_495_ = v_reuseFailAlloc_507_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v_newNode_496_; size_t v___x_497_; uint8_t v___x_498_; 
v_newNode_496_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(v___x_495_, v_x_441_, v_x_442_);
v___x_497_ = ((size_t)7ULL);
v___x_498_ = lean_usize_dec_le(v___x_497_, v_x_440_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_499_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_496_);
v___x_500_ = lean_unsigned_to_nat(4u);
v___x_501_ = lean_nat_dec_lt(v___x_499_, v___x_500_);
lean_dec(v___x_499_);
if (v___x_501_ == 0)
{
lean_object* v_ks_502_; lean_object* v_vs_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_ks_502_ = lean_ctor_get(v_newNode_496_, 0);
lean_inc_ref(v_ks_502_);
v_vs_503_ = lean_ctor_get(v_newNode_496_, 1);
lean_inc_ref(v_vs_503_);
lean_dec_ref(v_newNode_496_);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0);
v___x_506_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_x_440_, v_ks_502_, v_vs_503_, v___x_504_, v___x_505_);
lean_dec_ref(v_vs_503_);
lean_dec_ref(v_ks_502_);
return v___x_506_;
}
else
{
return v_newNode_496_;
}
}
else
{
return v_newNode_496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(size_t v_depth_509_, lean_object* v_keys_510_, lean_object* v_vals_511_, lean_object* v_i_512_, lean_object* v_entries_513_){
_start:
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_array_get_size(v_keys_510_);
v___x_515_ = lean_nat_dec_lt(v_i_512_, v___x_514_);
if (v___x_515_ == 0)
{
lean_dec(v_i_512_);
return v_entries_513_;
}
else
{
lean_object* v_k_516_; lean_object* v_v_517_; uint64_t v___x_518_; size_t v_h_519_; size_t v___x_520_; lean_object* v___x_521_; size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; size_t v_h_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_k_516_ = lean_array_fget_borrowed(v_keys_510_, v_i_512_);
v_v_517_ = lean_array_fget_borrowed(v_vals_511_, v_i_512_);
v___x_518_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_k_516_);
v_h_519_ = lean_uint64_to_usize(v___x_518_);
v___x_520_ = ((size_t)5ULL);
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_sub(v_depth_509_, v___x_522_);
v___x_524_ = lean_usize_mul(v___x_520_, v___x_523_);
v_h_525_ = lean_usize_shift_right(v_h_519_, v___x_524_);
v___x_526_ = lean_nat_add(v_i_512_, v___x_521_);
lean_dec(v_i_512_);
lean_inc(v_v_517_);
lean_inc(v_k_516_);
v___x_527_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_entries_513_, v_h_525_, v_depth_509_, v_k_516_, v_v_517_);
v_i_512_ = v___x_526_;
v_entries_513_ = v___x_527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg___boxed(lean_object* v_depth_529_, lean_object* v_keys_530_, lean_object* v_vals_531_, lean_object* v_i_532_, lean_object* v_entries_533_){
_start:
{
size_t v_depth_boxed_534_; lean_object* v_res_535_; 
v_depth_boxed_534_ = lean_unbox_usize(v_depth_529_);
lean_dec(v_depth_529_);
v_res_535_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_depth_boxed_534_, v_keys_530_, v_vals_531_, v_i_532_, v_entries_533_);
lean_dec_ref(v_vals_531_);
lean_dec_ref(v_keys_530_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
size_t v_x_21008__boxed_541_; size_t v_x_21009__boxed_542_; lean_object* v_res_543_; 
v_x_21008__boxed_541_ = lean_unbox_usize(v_x_537_);
lean_dec(v_x_537_);
v_x_21009__boxed_542_ = lean_unbox_usize(v_x_538_);
lean_dec(v_x_538_);
v_res_543_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_536_, v_x_21008__boxed_541_, v_x_21009__boxed_542_, v_x_539_, v_x_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
uint64_t v___x_547_; size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; 
v___x_547_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_545_);
v___x_548_ = lean_uint64_to_usize(v___x_547_);
v___x_549_ = ((size_t)1ULL);
v___x_550_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_544_, v___x_548_, v___x_549_, v_x_545_, v_x_546_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0(lean_object* v___x_551_, lean_object* v_a_552_, lean_object* v_s_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_s_553_, v___x_551_, v_a_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1(lean_object* v___x_555_, lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v_h_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; uint8_t v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; 
v___x_564_ = lean_array_push(v___x_555_, v_h_558_);
v___x_565_ = l_Lean_mkAppN(v___x_556_, v___x_557_);
v___x_566_ = 0;
v___x_567_ = 1;
v___x_568_ = 1;
v___x_569_ = l_Lean_Meta_mkForallFVars(v___x_564_, v___x_565_, v___x_566_, v___x_567_, v___x_567_, v___x_568_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec_ref(v___x_564_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(lean_object* v___x_570_, lean_object* v___x_571_, lean_object* v___x_572_, lean_object* v_h_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Meta_mkSparseCasesOn___lam__1(v___x_570_, v___x_571_, v___x_572_, v_h_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v___x_572_);
return v_res_579_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_instMonadEIO(lean_box(0));
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(lean_object* v_msg_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_toApplicative_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_654_; 
v___x_591_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0);
v___x_592_ = l_StateRefT_x27_instMonad___redArg(v___x_591_);
v_toApplicative_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v___x_592_, 1);
lean_dec(v_unused_655_);
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_654_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_toApplicative_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_654_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_toFunctor_597_; lean_object* v_toSeq_598_; lean_object* v_toSeqLeft_599_; lean_object* v_toSeqRight_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_652_; 
v_toFunctor_597_ = lean_ctor_get(v_toApplicative_593_, 0);
v_toSeq_598_ = lean_ctor_get(v_toApplicative_593_, 2);
v_toSeqLeft_599_ = lean_ctor_get(v_toApplicative_593_, 3);
v_toSeqRight_600_ = lean_ctor_get(v_toApplicative_593_, 4);
v_isSharedCheck_652_ = !lean_is_exclusive(v_toApplicative_593_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v_toApplicative_593_, 1);
lean_dec(v_unused_653_);
v___x_602_ = v_toApplicative_593_;
v_isShared_603_ = v_isSharedCheck_652_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_toSeqRight_600_);
lean_inc(v_toSeqLeft_599_);
lean_inc(v_toSeq_598_);
lean_inc(v_toFunctor_597_);
lean_dec(v_toApplicative_593_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_652_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___x_613_; 
v___f_604_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1));
v___f_605_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_597_);
v___f_606_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_606_, 0, v_toFunctor_597_);
v___f_607_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_607_, 0, v_toFunctor_597_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___f_606_);
lean_ctor_set(v___x_608_, 1, v___f_607_);
v___f_609_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_609_, 0, v_toSeqRight_600_);
v___f_610_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_610_, 0, v_toSeqLeft_599_);
v___f_611_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_611_, 0, v_toSeq_598_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 4, v___f_609_);
lean_ctor_set(v___x_602_, 3, v___f_610_);
lean_ctor_set(v___x_602_, 2, v___f_611_);
lean_ctor_set(v___x_602_, 1, v___f_604_);
lean_ctor_set(v___x_602_, 0, v___x_608_);
v___x_613_ = v___x_602_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___f_604_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v___f_611_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v___f_610_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v___f_609_);
v___x_613_ = v_reuseFailAlloc_651_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___f_605_);
lean_ctor_set(v___x_595_, 0, v___x_613_);
v___x_615_ = v___x_595_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___f_605_);
v___x_615_ = v_reuseFailAlloc_650_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v_toApplicative_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_648_; 
v___x_616_ = l_StateRefT_x27_instMonad___redArg(v___x_615_);
v_toApplicative_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v___x_616_, 1);
lean_dec(v_unused_649_);
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_648_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_toApplicative_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_648_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_toFunctor_621_; lean_object* v_toSeq_622_; lean_object* v_toSeqLeft_623_; lean_object* v_toSeqRight_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_646_; 
v_toFunctor_621_ = lean_ctor_get(v_toApplicative_617_, 0);
v_toSeq_622_ = lean_ctor_get(v_toApplicative_617_, 2);
v_toSeqLeft_623_ = lean_ctor_get(v_toApplicative_617_, 3);
v_toSeqRight_624_ = lean_ctor_get(v_toApplicative_617_, 4);
v_isSharedCheck_646_ = !lean_is_exclusive(v_toApplicative_617_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v_toApplicative_617_, 1);
lean_dec(v_unused_647_);
v___x_626_ = v_toApplicative_617_;
v_isShared_627_ = v_isSharedCheck_646_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_toSeqRight_624_);
lean_inc(v_toSeqLeft_623_);
lean_inc(v_toSeq_622_);
lean_inc(v_toFunctor_621_);
lean_dec(v_toApplicative_617_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_646_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___x_632_; lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___f_635_; lean_object* v___x_637_; 
v___f_628_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3));
v___f_629_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_621_);
v___f_630_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_630_, 0, v_toFunctor_621_);
v___f_631_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_631_, 0, v_toFunctor_621_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___f_630_);
lean_ctor_set(v___x_632_, 1, v___f_631_);
v___f_633_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_633_, 0, v_toSeqRight_624_);
v___f_634_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_634_, 0, v_toSeqLeft_623_);
v___f_635_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_635_, 0, v_toSeq_622_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 4, v___f_633_);
lean_ctor_set(v___x_626_, 3, v___f_634_);
lean_ctor_set(v___x_626_, 2, v___f_635_);
lean_ctor_set(v___x_626_, 1, v___f_628_);
lean_ctor_set(v___x_626_, 0, v___x_632_);
v___x_637_ = v___x_626_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___f_628_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v___f_635_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v___f_634_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v___f_633_);
v___x_637_ = v_reuseFailAlloc_645_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___f_629_);
lean_ctor_set(v___x_619_, 0, v___x_637_);
v___x_639_ = v___x_619_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___f_629_);
v___x_639_ = v_reuseFailAlloc_644_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_17122__overap_642_; lean_object* v___x_643_; 
v___x_640_ = lean_box(0);
v___x_641_ = l_instInhabitedOfMonad___redArg(v___x_639_, v___x_640_);
v___x_17122__overap_642_ = lean_panic_fn_borrowed(v___x_641_, v_msg_585_);
lean_dec(v___x_641_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
v___x_643_ = lean_apply_5(v___x_17122__overap_642_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, lean_box(0));
return v___x_643_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v_msg_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(lean_object* v_msgData_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_669_; lean_object* v_env_670_; lean_object* v___x_671_; lean_object* v_mctx_672_; lean_object* v_lctx_673_; lean_object* v_options_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_669_ = lean_st_ref_get(v___y_667_);
v_env_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc_ref(v_env_670_);
lean_dec(v___x_669_);
v___x_671_ = lean_st_ref_get(v___y_665_);
v_mctx_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref(v_mctx_672_);
lean_dec(v___x_671_);
v_lctx_673_ = lean_ctor_get(v___y_664_, 2);
v_options_674_ = lean_ctor_get(v___y_666_, 2);
lean_inc_ref(v_options_674_);
lean_inc_ref(v_lctx_673_);
v___x_675_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_675_, 0, v_env_670_);
lean_ctor_set(v___x_675_, 1, v_mctx_672_);
lean_ctor_set(v___x_675_, 2, v_lctx_673_);
lean_ctor_set(v___x_675_, 3, v_options_674_);
v___x_676_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v_msgData_663_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19___boxed(lean_object* v_msgData_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(v_msgData_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(lean_object* v_msg_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_ref_691_; lean_object* v___x_692_; lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_ref_691_ = lean_ctor_get(v___y_688_, 5);
v___x_692_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(v_msg_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
lean_inc(v_ref_691_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_ref_691_);
lean_ctor_set(v___x_697_, 1, v_a_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set_tag(v___x_695_, 1);
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
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
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg___boxed(lean_object* v_msg_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
return v_res_708_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0));
v___x_711_ = l_Lean_stringToMessageData(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_718_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6));
v___x_719_ = lean_unsigned_to_nat(11u);
v___x_720_ = lean_unsigned_to_nat(122u);
v___x_721_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5));
v___x_722_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4));
v___x_723_ = l_mkPanicMessageWithDecl(v___x_722_, v___x_721_, v___x_720_, v___x_719_, v___x_718_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object* v_constName_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_738_; lean_object* v_env_739_; uint8_t v___x_740_; lean_object* v___x_741_; 
v___x_738_ = lean_st_ref_get(v___y_728_);
v_env_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_ref(v_env_739_);
lean_dec(v___x_738_);
v___x_740_ = 0;
lean_inc(v_constName_724_);
v___x_741_ = l_Lean_Environment_findAsync_x3f(v_env_739_, v_constName_724_, v___x_740_);
if (lean_obj_tag(v___x_741_) == 1)
{
lean_object* v_val_742_; uint8_t v_kind_743_; 
v_val_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v___x_741_, 1);
v_kind_743_ = lean_ctor_get_uint8(v_val_742_, sizeof(void*)*3);
if (v_kind_743_ == 6)
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_742_);
if (lean_obj_tag(v___x_744_) == 6)
{
lean_object* v_val_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_constName_724_);
v_val_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_val_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 0);
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_val_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v___x_744_);
v___x_753_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7);
v___x_754_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v___x_753_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_763_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
if (lean_obj_tag(v_a_755_) == 0)
{
lean_del_object(v___x_757_);
goto v___jp_730_;
}
else
{
lean_object* v_val_759_; lean_object* v___x_761_; 
lean_dec(v_constName_724_);
v_val_759_ = lean_ctor_get(v_a_755_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v_a_755_, 1);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v_val_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_val_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_constName_724_);
v_a_764_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_754_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_754_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
else
{
lean_dec(v_val_742_);
goto v___jp_730_;
}
}
else
{
lean_dec(v___x_741_);
goto v___jp_730_;
}
v___jp_730_:
{
lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_731_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_732_ = 0;
v___x_733_ = l_Lean_MessageData_ofConstName(v_constName_724_, v___x_732_);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_731_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_736_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object* v_constName_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_constName_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object* v___x_779_, size_t v_sz_780_, size_t v_i_781_, lean_object* v_bs_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = lean_usize_dec_lt(v_i_781_, v_sz_780_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v_bs_782_);
return v___x_789_;
}
else
{
lean_object* v_v_790_; lean_object* v___x_791_; 
v_v_790_ = lean_array_uget_borrowed(v_bs_782_, v_i_781_);
lean_inc(v_v_790_);
v___x_791_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_790_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v_cidx_793_; lean_object* v_start_794_; lean_object* v_stop_795_; lean_object* v___x_796_; lean_object* v_bs_x27_797_; lean_object* v_a_799_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v_cidx_793_ = lean_ctor_get(v_a_792_, 2);
lean_inc(v_cidx_793_);
lean_dec(v_a_792_);
v_start_794_ = lean_ctor_get(v___x_779_, 1);
v_stop_795_ = lean_ctor_get(v___x_779_, 2);
v___x_796_ = lean_unsigned_to_nat(0u);
v_bs_x27_797_ = lean_array_uset(v_bs_782_, v_i_781_, v___x_796_);
v___x_804_ = lean_nat_sub(v_stop_795_, v_start_794_);
v___x_805_ = lean_nat_dec_lt(v_cidx_793_, v___x_804_);
lean_dec(v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v_cidx_793_);
v___x_806_ = l_Lean_instInhabitedExpr;
v___x_807_ = l_outOfBounds___redArg(v___x_806_);
v_a_799_ = v___x_807_;
goto v___jp_798_;
}
else
{
lean_object* v___x_808_; 
v___x_808_ = l_Subarray_get___redArg(v___x_779_, v_cidx_793_);
lean_dec(v_cidx_793_);
v_a_799_ = v___x_808_;
goto v___jp_798_;
}
v___jp_798_:
{
size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_add(v_i_781_, v___x_800_);
v___x_802_ = lean_array_uset(v_bs_x27_797_, v_i_781_, v_a_799_);
v_i_781_ = v___x_801_;
v_bs_782_ = v___x_802_;
goto _start;
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_bs_782_);
v_a_809_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_791_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_791_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7___boxed(lean_object* v___x_817_, lean_object* v_sz_818_, lean_object* v_i_819_, lean_object* v_bs_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
size_t v_sz_boxed_826_; size_t v_i_boxed_827_; lean_object* v_res_828_; 
v_sz_boxed_826_ = lean_unbox_usize(v_sz_818_);
lean_dec(v_sz_818_);
v_i_boxed_827_ = lean_unbox_usize(v_i_819_);
lean_dec(v_i_819_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(v___x_817_, v_sz_boxed_826_, v_i_boxed_827_, v_bs_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v___x_817_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(lean_object* v_xs_829_, lean_object* v_v_830_, lean_object* v_i_831_){
_start:
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_array_get_size(v_xs_829_);
v___x_833_ = lean_nat_dec_lt(v_i_831_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v_i_831_);
v___x_834_ = lean_box(0);
return v___x_834_;
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_array_fget_borrowed(v_xs_829_, v_i_831_);
v___x_836_ = lean_name_eq(v___x_835_, v_v_830_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_add(v_i_831_, v___x_837_);
lean_dec(v_i_831_);
v_i_831_ = v___x_838_;
goto _start;
}
else
{
lean_object* v___x_840_; 
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v_i_831_);
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23___boxed(lean_object* v_xs_841_, lean_object* v_v_842_, lean_object* v_i_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(v_xs_841_, v_v_842_, v_i_843_);
lean_dec(v_v_842_);
lean_dec_ref(v_xs_841_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(lean_object* v_xs_845_, lean_object* v_v_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(v_xs_845_, v_v_846_, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15___boxed(lean_object* v_xs_849_, lean_object* v_v_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(v_xs_849_, v_v_850_);
lean_dec(v_v_850_);
lean_dec_ref(v_xs_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object* v_xs_852_, lean_object* v_v_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(v_xs_852_, v_v_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v___x_855_; 
v___x_855_ = lean_box(0);
return v___x_855_;
}
else
{
lean_object* v_val_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_val_856_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_854_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_val_856_);
lean_dec(v___x_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_val_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object* v_xs_864_, lean_object* v_v_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(v_xs_864_, v_v_865_);
lean_dec(v_v_865_);
lean_dec_ref(v_xs_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(lean_object* v_ctors_867_, lean_object* v_a_868_, lean_object* v___x_869_, lean_object* v_a_870_, uint8_t v___x_871_, uint8_t v___x_872_, lean_object* v_a_873_, lean_object* v_ys_874_, lean_object* v_x_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(v_ctors_867_, v_a_868_);
if (lean_obj_tag(v___x_881_) == 1)
{
lean_object* v_val_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; 
lean_dec(v_a_868_);
v_val_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v___x_881_, 1);
lean_inc_ref(v_ys_874_);
v___x_883_ = lean_array_pop(v_ys_874_);
v___x_884_ = lean_array_get_borrowed(v___x_869_, v_a_870_, v_val_882_);
lean_dec(v_val_882_);
lean_inc(v___x_884_);
v___x_885_ = l_Lean_mkAppN(v___x_884_, v___x_883_);
lean_dec_ref(v___x_883_);
v___x_886_ = 1;
v___x_887_ = l_Lean_Meta_mkLambdaFVars(v_ys_874_, v___x_885_, v___x_871_, v___x_872_, v___x_871_, v___x_872_, v___x_886_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec_ref(v_ys_874_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; 
lean_dec(v___x_881_);
v___x_888_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_a_868_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v_cidx_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v_cidx_890_ = lean_ctor_get(v_a_889_, 2);
lean_inc(v_cidx_890_);
lean_dec(v_a_889_);
v___x_891_ = l_Lean_mkRawNatLit(v_cidx_890_);
v___x_892_ = l_Lean_mkHasNotBitProof(v___x_891_, v_a_873_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = lean_array_get_size(v_ys_874_);
v___x_895_ = lean_unsigned_to_nat(1u);
v___x_896_ = lean_nat_sub(v___x_894_, v___x_895_);
v___x_897_ = lean_array_get_borrowed(v___x_869_, v_ys_874_, v___x_896_);
lean_dec(v___x_896_);
lean_inc(v___x_897_);
v___x_898_ = l_Lean_Expr_app___override(v___x_897_, v_a_893_);
v___x_899_ = 1;
v___x_900_ = l_Lean_Meta_mkLambdaFVars(v_ys_874_, v___x_898_, v___x_871_, v___x_872_, v___x_871_, v___x_872_, v___x_899_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec_ref(v_ys_874_);
return v___x_900_;
}
else
{
lean_dec_ref(v_ys_874_);
return v___x_892_;
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_ys_874_);
v_a_901_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_888_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_888_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0___boxed(lean_object* v_ctors_909_, lean_object* v_a_910_, lean_object* v___x_911_, lean_object* v_a_912_, lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v_a_915_, lean_object* v_ys_916_, lean_object* v_x_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
uint8_t v___x_21666__boxed_923_; uint8_t v___x_21667__boxed_924_; lean_object* v_res_925_; 
v___x_21666__boxed_923_ = lean_unbox(v___x_913_);
v___x_21667__boxed_924_ = lean_unbox(v___x_914_);
v_res_925_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(v_ctors_909_, v_a_910_, v___x_911_, v_a_912_, v___x_21666__boxed_923_, v___x_21667__boxed_924_, v_a_915_, v_ys_916_, v_x_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec_ref(v_x_917_);
lean_dec_ref(v_a_915_);
lean_dec_ref(v_a_912_);
lean_dec_ref(v___x_911_);
lean_dec_ref(v_ctors_909_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object* v_ctors_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_as_929_, lean_object* v_bs_930_, lean_object* v_i_931_, lean_object* v_cs_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_array_get_size(v_as_929_);
v___x_939_ = lean_nat_dec_lt(v_i_931_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
lean_dec(v_i_931_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec_ref(v_ctors_926_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_cs_932_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = lean_array_get_size(v_bs_930_);
v___x_942_ = lean_nat_dec_lt(v_i_931_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_dec(v_i_931_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec_ref(v_ctors_926_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_cs_932_);
return v___x_943_;
}
else
{
lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v_a_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___f_949_; lean_object* v_b_950_; lean_object* v___x_951_; 
v___x_944_ = l_Lean_instInhabitedExpr;
v___x_945_ = 0;
v_a_946_ = lean_array_fget_borrowed(v_as_929_, v_i_931_);
v___x_947_ = lean_box(v___x_945_);
v___x_948_ = lean_box(v___x_942_);
lean_inc_ref(v_a_928_);
lean_inc_ref(v_a_927_);
lean_inc(v_a_946_);
lean_inc_ref(v_ctors_926_);
v___f_949_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_949_, 0, v_ctors_926_);
lean_closure_set(v___f_949_, 1, v_a_946_);
lean_closure_set(v___f_949_, 2, v___x_944_);
lean_closure_set(v___f_949_, 3, v_a_927_);
lean_closure_set(v___f_949_, 4, v___x_947_);
lean_closure_set(v___f_949_, 5, v___x_948_);
lean_closure_set(v___f_949_, 6, v_a_928_);
v_b_950_ = lean_array_fget_borrowed(v_bs_930_, v_i_931_);
lean_inc(v_b_950_);
v___x_951_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v_b_950_, v___f_949_, v___x_945_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_add(v_i_931_, v___x_953_);
lean_dec(v_i_931_);
v___x_955_ = lean_array_push(v_cs_932_, v_a_952_);
v_i_931_ = v___x_954_;
v_cs_932_ = v___x_955_;
goto _start;
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v_cs_932_);
lean_dec(v_i_931_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec_ref(v_ctors_926_);
v_a_957_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_951_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_951_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object* v_ctors_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_as_968_, lean_object* v_bs_969_, lean_object* v_i_970_, lean_object* v_cs_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(v_ctors_965_, v_a_966_, v_a_967_, v_as_968_, v_bs_969_, v_i_970_, v_cs_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec_ref(v_bs_969_);
lean_dec_ref(v_as_968_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(size_t v_sz_978_, size_t v_i_979_, lean_object* v_bs_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
uint8_t v___x_986_; 
v___x_986_ = lean_usize_dec_lt(v_i_979_, v_sz_978_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_bs_980_);
return v___x_987_;
}
else
{
lean_object* v_v_988_; lean_object* v___x_989_; 
v_v_988_ = lean_array_uget_borrowed(v_bs_980_, v_i_979_);
lean_inc(v_v_988_);
v___x_989_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_988_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v_cidx_991_; lean_object* v___x_992_; lean_object* v_bs_x27_993_; size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v_cidx_991_ = lean_ctor_get(v_a_990_, 2);
lean_inc(v_cidx_991_);
lean_dec(v_a_990_);
v___x_992_ = lean_unsigned_to_nat(0u);
v_bs_x27_993_ = lean_array_uset(v_bs_980_, v_i_979_, v___x_992_);
v___x_994_ = ((size_t)1ULL);
v___x_995_ = lean_usize_add(v_i_979_, v___x_994_);
v___x_996_ = lean_array_uset(v_bs_x27_993_, v_i_979_, v_cidx_991_);
v_i_979_ = v___x_995_;
v_bs_980_ = v___x_996_;
goto _start;
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v_bs_980_);
v_a_998_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_989_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_989_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object* v_sz_1006_, lean_object* v_i_1007_, lean_object* v_bs_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
size_t v_sz_boxed_1014_; size_t v_i_boxed_1015_; lean_object* v_res_1016_; 
v_sz_boxed_1014_ = lean_unbox_usize(v_sz_1006_);
lean_dec(v_sz_1006_);
v_i_boxed_1015_ = lean_unbox_usize(v_i_1007_);
lean_dec(v_i_1007_);
v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v_sz_boxed_1014_, v_i_boxed_1015_, v_bs_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0(lean_object* v_k_1017_, lean_object* v_b_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
v___x_1024_ = lean_apply_6(v_k_1017_, v_b_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0___boxed(lean_object* v_k_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0(v_k_1025_, v_b_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(lean_object* v_name_1033_, uint8_t v_bi_1034_, lean_object* v_type_1035_, lean_object* v_k_1036_, uint8_t v_kind_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___f_1043_; lean_object* v___x_1044_; 
v___f_1043_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1043_, 0, v_k_1036_);
v___x_1044_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1033_, v_bi_1034_, v_type_1035_, v___f_1043_, v_kind_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
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
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1044_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1044_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___boxed(lean_object* v_name_1061_, lean_object* v_bi_1062_, lean_object* v_type_1063_, lean_object* v_k_1064_, lean_object* v_kind_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
uint8_t v_bi_boxed_1071_; uint8_t v_kind_boxed_1072_; lean_object* v_res_1073_; 
v_bi_boxed_1071_ = lean_unbox(v_bi_1062_);
v_kind_boxed_1072_ = lean_unbox(v_kind_1065_);
v_res_1073_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_1061_, v_bi_boxed_1071_, v_type_1063_, v_k_1064_, v_kind_boxed_1072_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(lean_object* v_name_1074_, lean_object* v_type_1075_, lean_object* v_k_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
uint8_t v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = 0;
v___x_1083_ = 0;
v___x_1084_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_1074_, v___x_1082_, v_type_1075_, v_k_1076_, v___x_1083_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg___boxed(lean_object* v_name_1085_, lean_object* v_type_1086_, lean_object* v_k_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v_name_1085_, v_type_1086_, v_k_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1093_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object* v_numParams_1105_, lean_object* v___x_1106_, lean_object* v_numIndices_1107_, lean_object* v_ctors_1108_, lean_object* v___x_1109_, lean_object* v___x_1110_, lean_object* v_a_1111_, lean_object* v_ctors_1112_, lean_object* v___x_1113_, lean_object* v_xs_1114_, lean_object* v_x_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1229_ = lean_array_get_size(v_xs_1114_);
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_add(v_numParams_1105_, v___x_1230_);
v___x_1232_ = lean_nat_add(v___x_1231_, v_numIndices_1107_);
lean_dec(v___x_1231_);
v___x_1233_ = lean_nat_add(v___x_1232_, v___x_1230_);
lean_dec(v___x_1232_);
v___x_1234_ = l_List_lengthTR___redArg(v_ctors_1112_);
v___x_1235_ = lean_nat_add(v___x_1233_, v___x_1234_);
lean_dec(v___x_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_nat_dec_eq(v___x_1229_, v___x_1235_);
lean_dec(v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v_xs_1114_);
lean_dec(v_ctors_1112_);
lean_dec(v___x_1110_);
lean_dec(v___x_1109_);
lean_dec_ref(v_ctors_1108_);
lean_dec(v_numParams_1105_);
v___x_1237_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6, &l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once, _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6);
v___x_1238_ = l_Lean_MessageData_ofConstName(v___x_1113_, v___x_1236_);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_1241_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
lean_dec(v___x_1113_);
v___y_1122_ = v___y_1116_;
v___y_1123_ = v___y_1117_;
v___y_1124_ = v___y_1118_;
v___y_1125_ = v___y_1119_;
goto v___jp_1121_;
}
v___jp_1121_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; size_t v_sz_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1126_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1105_);
lean_inc_ref_n(v_xs_1114_, 2);
v___x_1127_ = l_Array_toSubarray___redArg(v_xs_1114_, v___x_1126_, v_numParams_1105_);
v___x_1128_ = lean_array_get(v___x_1106_, v_xs_1114_, v_numParams_1105_);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_nat_add(v_numParams_1105_, v___x_1129_);
lean_dec(v_numParams_1105_);
v___x_1131_ = lean_nat_add(v___x_1130_, v_numIndices_1107_);
lean_inc(v___x_1131_);
v___x_1132_ = l_Array_toSubarray___redArg(v_xs_1114_, v___x_1130_, v___x_1131_);
v___x_1133_ = lean_array_get(v___x_1106_, v_xs_1114_, v___x_1131_);
v___x_1134_ = lean_nat_add(v___x_1131_, v___x_1129_);
lean_dec(v___x_1131_);
v___x_1135_ = lean_array_get_size(v_xs_1114_);
v___x_1136_ = l_Array_toSubarray___redArg(v_xs_1114_, v___x_1134_, v___x_1135_);
v_sz_1137_ = lean_array_size(v_ctors_1108_);
v___x_1138_ = ((size_t)0ULL);
lean_inc_ref(v_ctors_1108_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(v___x_1136_, v_sz_1137_, v___x_1138_, v_ctors_1108_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec_ref(v___x_1136_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
lean_inc_ref(v_ctors_1108_);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v_sz_1137_, v___x_1138_, v_ctors_1108_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___f_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = l_Subarray_copy___redArg(v___x_1132_);
v___x_1144_ = lean_mk_empty_array_with_capacity(v___x_1129_);
lean_inc(v___x_1133_);
lean_inc_ref_n(v___x_1144_, 2);
v___x_1145_ = lean_array_push(v___x_1144_, v___x_1133_);
lean_inc_ref(v___x_1143_);
v___x_1146_ = l_Array_append___redArg(v___x_1143_, v___x_1145_);
lean_inc_ref(v___x_1146_);
lean_inc(v___x_1128_);
v___f_1147_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1147_, 0, v___x_1144_);
lean_closure_set(v___f_1147_, 1, v___x_1128_);
lean_closure_set(v___f_1147_, 2, v___x_1146_);
v___x_1148_ = l_Lean_mkConst(v___x_1109_, v___x_1110_);
v___x_1149_ = l_Subarray_copy___redArg(v___x_1127_);
lean_inc_ref(v___x_1149_);
v___x_1150_ = l_Array_append___redArg(v___x_1149_, v___x_1143_);
v___x_1151_ = l_Array_append___redArg(v___x_1150_, v___x_1145_);
v___x_1152_ = l_Lean_mkAppN(v___x_1148_, v___x_1151_);
lean_dec_ref(v___x_1151_);
v___x_1153_ = l_Lean_mkHasNotBit(v___x_1152_, v_a_1142_);
v___x_1154_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1));
v___x_1155_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v___x_1154_, v___x_1153_, v___f_1147_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3));
v___x_1158_ = l_Lean_Core_mkFreshUserName(v___x_1157_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = 0;
v___x_1161_ = l_Lean_ConstantInfo_value_x21(v_a_1111_, v___x_1160_);
v___x_1162_ = 0;
lean_inc(v___x_1128_);
v___x_1163_ = l_Lean_mkAppN(v___x_1128_, v___x_1146_);
v___x_1164_ = l_Lean_mkForall(v_a_1159_, v___x_1162_, v_a_1156_, v___x_1163_);
v___x_1165_ = 1;
v___x_1166_ = 1;
v___x_1167_ = l_Lean_Meta_mkLambdaFVars(v___x_1146_, v___x_1164_, v___x_1160_, v___x_1165_, v___x_1160_, v___x_1165_, v___x_1166_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec_ref(v___x_1146_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = l_Lean_mkAppN(v___x_1161_, v___x_1149_);
v___x_1170_ = l_Lean_Expr_app___override(v___x_1169_, v_a_1168_);
v___x_1171_ = l_Lean_mkAppN(v___x_1170_, v___x_1143_);
v___x_1172_ = l_Lean_Expr_app___override(v___x_1171_, v___x_1133_);
v___x_1173_ = l_List_lengthTR___redArg(v_ctors_1112_);
lean_inc_ref(v___x_1172_);
v___x_1174_ = l_Lean_Meta_inferArgumentTypesN(v___x_1173_, v___x_1172_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = lean_array_mk(v_ctors_1112_);
v___x_1177_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4));
lean_inc(v_a_1140_);
v___x_1178_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(v_ctors_1108_, v_a_1140_, v_a_1142_, v___x_1176_, v_a_1175_, v___x_1126_, v___x_1177_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v_a_1175_);
lean_dec_ref(v___x_1176_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v___x_1180_ = l_Lean_mkAppN(v___x_1172_, v_a_1179_);
lean_dec(v_a_1179_);
v___x_1181_ = l_Lean_Core_betaReduce(v___x_1180_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = lean_array_push(v___x_1144_, v___x_1128_);
v___x_1184_ = l_Array_append___redArg(v___x_1149_, v___x_1183_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = l_Array_append___redArg(v___x_1184_, v___x_1143_);
lean_dec_ref(v___x_1143_);
v___x_1186_ = l_Array_append___redArg(v___x_1185_, v___x_1145_);
lean_dec_ref(v___x_1145_);
v___x_1187_ = l_Array_append___redArg(v___x_1186_, v_a_1140_);
lean_dec(v_a_1140_);
v___x_1188_ = l_Lean_Meta_mkLambdaFVars(v___x_1187_, v_a_1182_, v___x_1160_, v___x_1165_, v___x_1160_, v___x_1165_, v___x_1166_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec_ref(v___x_1187_);
return v___x_1188_;
}
else
{
lean_dec_ref(v___x_1149_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___x_1143_);
lean_dec(v_a_1140_);
lean_dec(v___x_1128_);
return v___x_1181_;
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v___x_1172_);
lean_dec_ref(v___x_1149_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___x_1143_);
lean_dec(v_a_1140_);
lean_dec(v___x_1128_);
v_a_1189_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1178_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1178_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v___x_1172_);
lean_dec_ref(v___x_1149_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___x_1143_);
lean_dec(v_a_1142_);
lean_dec(v_a_1140_);
lean_dec(v___x_1128_);
lean_dec(v_ctors_1112_);
lean_dec_ref(v_ctors_1108_);
v_a_1197_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1174_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1174_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_dec_ref(v___x_1161_);
lean_dec_ref(v___x_1149_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___x_1143_);
lean_dec(v_a_1142_);
lean_dec(v_a_1140_);
lean_dec(v___x_1133_);
lean_dec(v___x_1128_);
lean_dec(v_ctors_1112_);
lean_dec_ref(v_ctors_1108_);
return v___x_1167_;
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_a_1156_);
lean_dec_ref(v___x_1149_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___x_1143_);
lean_dec(v_a_1142_);
lean_dec(v_a_1140_);
lean_dec(v___x_1133_);
lean_dec(v___x_1128_);
lean_dec(v_ctors_1112_);
lean_dec_ref(v_ctors_1108_);
v_a_1205_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1158_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1158_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_dec_ref(v___x_1149_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___x_1143_);
lean_dec(v_a_1142_);
lean_dec(v_a_1140_);
lean_dec(v___x_1133_);
lean_dec(v___x_1128_);
lean_dec(v_ctors_1112_);
lean_dec_ref(v_ctors_1108_);
return v___x_1155_;
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v_a_1140_);
lean_dec(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec(v___x_1128_);
lean_dec_ref(v___x_1127_);
lean_dec(v_ctors_1112_);
lean_dec(v___x_1110_);
lean_dec(v___x_1109_);
lean_dec_ref(v_ctors_1108_);
v_a_1213_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1141_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1141_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec(v___x_1128_);
lean_dec_ref(v___x_1127_);
lean_dec(v_ctors_1112_);
lean_dec(v___x_1110_);
lean_dec(v___x_1109_);
lean_dec_ref(v_ctors_1108_);
v_a_1221_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1139_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1139_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object* v_numParams_1251_, lean_object* v___x_1252_, lean_object* v_numIndices_1253_, lean_object* v_ctors_1254_, lean_object* v___x_1255_, lean_object* v___x_1256_, lean_object* v_a_1257_, lean_object* v_ctors_1258_, lean_object* v___x_1259_, lean_object* v_xs_1260_, lean_object* v_x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Meta_mkSparseCasesOn___lam__2(v_numParams_1251_, v___x_1252_, v_numIndices_1253_, v_ctors_1254_, v___x_1255_, v___x_1256_, v_a_1257_, v_ctors_1258_, v___x_1259_, v_xs_1260_, v_x_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec_ref(v_x_1261_);
lean_dec_ref(v_a_1257_);
lean_dec(v_numIndices_1253_);
lean_dec_ref(v___x_1252_);
return v_res_1267_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object* v_a_1268_, lean_object* v_x_1269_){
_start:
{
if (lean_obj_tag(v_x_1269_) == 0)
{
uint8_t v___x_1270_; 
v___x_1270_ = 0;
return v___x_1270_;
}
else
{
lean_object* v_head_1271_; lean_object* v_tail_1272_; uint8_t v___x_1273_; 
v_head_1271_ = lean_ctor_get(v_x_1269_, 0);
v_tail_1272_ = lean_ctor_get(v_x_1269_, 1);
v___x_1273_ = lean_name_eq(v_a_1268_, v_head_1271_);
if (v___x_1273_ == 0)
{
v_x_1269_ = v_tail_1272_;
goto _start;
}
else
{
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object* v_a_1275_, lean_object* v_x_1276_){
_start:
{
uint8_t v_res_1277_; lean_object* v_r_1278_; 
v_res_1277_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_a_1275_, v_x_1276_);
lean_dec(v_x_1276_);
lean_dec(v_a_1275_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2));
v___x_1284_ = l_Lean_stringToMessageData(v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object* v_a_1285_, lean_object* v_indName_1286_, lean_object* v_as_1287_, size_t v_sz_1288_, size_t v_i_1289_, lean_object* v_b_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_a_1297_; uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_lt(v_i_1289_, v_sz_1288_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec(v_indName_1286_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_b_1290_);
return v___x_1302_;
}
else
{
lean_object* v_ctors_1303_; lean_object* v___x_1304_; lean_object* v_a_1305_; uint8_t v___x_1306_; 
v_ctors_1303_ = lean_ctor_get(v_a_1285_, 4);
v___x_1304_ = lean_box(0);
v_a_1305_ = lean_array_uget_borrowed(v_as_1287_, v_i_1289_);
v___x_1306_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_a_1305_, v_ctors_1303_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1307_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1);
lean_inc(v_a_1305_);
v___x_1308_ = l_Lean_MessageData_ofName(v_a_1305_);
v___x_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
lean_inc(v_indName_1286_);
v___x_1312_ = l_Lean_MessageData_ofName(v_indName_1286_);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_1313_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_dec_ref_known(v___x_1314_, 1);
v_a_1297_ = v___x_1304_;
goto v___jp_1296_;
}
else
{
lean_dec(v_indName_1286_);
return v___x_1314_;
}
}
else
{
v_a_1297_ = v___x_1304_;
goto v___jp_1296_;
}
}
v___jp_1296_:
{
size_t v___x_1298_; size_t v___x_1299_; 
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_add(v_i_1289_, v___x_1298_);
v_i_1289_ = v___x_1299_;
v_b_1290_ = v_a_1297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object* v_a_1315_, lean_object* v_indName_1316_, lean_object* v_as_1317_, lean_object* v_sz_1318_, lean_object* v_i_1319_, lean_object* v_b_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
size_t v_sz_boxed_1326_; size_t v_i_boxed_1327_; lean_object* v_res_1328_; 
v_sz_boxed_1326_ = lean_unbox_usize(v_sz_1318_);
lean_dec(v_sz_1318_);
v_i_boxed_1327_ = lean_unbox_usize(v_i_1319_);
lean_dec(v_i_1319_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_1315_, v_indName_1316_, v_as_1317_, v_sz_boxed_1326_, v_i_boxed_1327_, v_b_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v_as_1317_);
lean_dec_ref(v_a_1315_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
if (lean_obj_tag(v_a_1329_) == 0)
{
lean_object* v___x_1331_; 
v___x_1331_ = l_List_reverse___redArg(v_a_1330_);
return v___x_1331_;
}
else
{
lean_object* v_head_1332_; lean_object* v_tail_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1342_; 
v_head_1332_ = lean_ctor_get(v_a_1329_, 0);
v_tail_1333_ = lean_ctor_get(v_a_1329_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_a_1329_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1335_ = v_a_1329_;
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_tail_1333_);
lean_inc(v_head_1332_);
lean_dec(v_a_1329_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = l_Lean_mkLevelParam(v_head_1332_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 1, v_a_1330_);
lean_ctor_set(v___x_1335_, 0, v___x_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_a_1330_);
v___x_1339_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
v_a_1329_ = v_tail_1333_;
v_a_1330_ = v___x_1339_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0);
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1);
v___x_1349_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
lean_ctor_set(v___x_1349_, 2, v___x_1348_);
lean_ctor_set(v___x_1349_, 3, v___x_1348_);
lean_ctor_set(v___x_1349_, 4, v___x_1348_);
lean_ctor_set(v___x_1349_, 5, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(lean_object* v_declName_1350_, uint8_t v_s_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v_env_1356_; lean_object* v_nextMacroScope_1357_; lean_object* v_ngen_1358_; lean_object* v_auxDeclNGen_1359_; lean_object* v_traceState_1360_; lean_object* v_messages_1361_; lean_object* v_infoState_1362_; lean_object* v_snapshotTasks_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1392_; 
v___x_1355_ = lean_st_ref_take(v___y_1353_);
v_env_1356_ = lean_ctor_get(v___x_1355_, 0);
v_nextMacroScope_1357_ = lean_ctor_get(v___x_1355_, 1);
v_ngen_1358_ = lean_ctor_get(v___x_1355_, 2);
v_auxDeclNGen_1359_ = lean_ctor_get(v___x_1355_, 3);
v_traceState_1360_ = lean_ctor_get(v___x_1355_, 4);
v_messages_1361_ = lean_ctor_get(v___x_1355_, 6);
v_infoState_1362_ = lean_ctor_get(v___x_1355_, 7);
v_snapshotTasks_1363_ = lean_ctor_get(v___x_1355_, 8);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1355_, 5);
lean_dec(v_unused_1393_);
v___x_1365_ = v___x_1355_;
v_isShared_1366_ = v_isSharedCheck_1392_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_snapshotTasks_1363_);
lean_inc(v_infoState_1362_);
lean_inc(v_messages_1361_);
lean_inc(v_traceState_1360_);
lean_inc(v_auxDeclNGen_1359_);
lean_inc(v_ngen_1358_);
lean_inc(v_nextMacroScope_1357_);
lean_inc(v_env_1356_);
lean_dec(v___x_1355_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1392_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
uint8_t v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1367_ = 0;
v___x_1368_ = lean_box(0);
v___x_1369_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1356_, v_declName_1350_, v_s_1351_, v___x_1367_, v___x_1368_);
v___x_1370_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 5, v___x_1370_);
lean_ctor_set(v___x_1365_, 0, v___x_1369_);
v___x_1372_ = v___x_1365_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_nextMacroScope_1357_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_ngen_1358_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_auxDeclNGen_1359_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_traceState_1360_);
lean_ctor_set(v_reuseFailAlloc_1391_, 5, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1391_, 6, v_messages_1361_);
lean_ctor_set(v_reuseFailAlloc_1391_, 7, v_infoState_1362_);
lean_ctor_set(v_reuseFailAlloc_1391_, 8, v_snapshotTasks_1363_);
v___x_1372_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v_mctx_1375_; lean_object* v_zetaDeltaFVarIds_1376_; lean_object* v_postponed_1377_; lean_object* v_diag_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1389_; 
v___x_1373_ = lean_st_ref_put(v___y_1353_, v___x_1372_);
v___x_1374_ = lean_st_ref_take(v___y_1352_);
v_mctx_1375_ = lean_ctor_get(v___x_1374_, 0);
v_zetaDeltaFVarIds_1376_ = lean_ctor_get(v___x_1374_, 2);
v_postponed_1377_ = lean_ctor_get(v___x_1374_, 3);
v_diag_1378_ = lean_ctor_get(v___x_1374_, 4);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; 
v_unused_1390_ = lean_ctor_get(v___x_1374_, 1);
lean_dec(v_unused_1390_);
v___x_1380_ = v___x_1374_;
v_isShared_1381_ = v_isSharedCheck_1389_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_diag_1378_);
lean_inc(v_postponed_1377_);
lean_inc(v_zetaDeltaFVarIds_1376_);
lean_inc(v_mctx_1375_);
lean_dec(v___x_1374_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1389_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v___x_1382_);
v___x_1384_ = v___x_1380_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_mctx_1375_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_zetaDeltaFVarIds_1376_);
lean_ctor_set(v_reuseFailAlloc_1388_, 3, v_postponed_1377_);
lean_ctor_set(v_reuseFailAlloc_1388_, 4, v_diag_1378_);
v___x_1384_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = lean_st_ref_put(v___y_1352_, v___x_1384_);
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___boxed(lean_object* v_declName_1394_, lean_object* v_s_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
uint8_t v_s_boxed_1399_; lean_object* v_res_1400_; 
v_s_boxed_1399_ = lean_unbox(v_s_1395_);
v_res_1400_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_1394_, v_s_boxed_1399_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec(v___y_1396_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object* v_declName_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = 0;
v___x_1408_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_1401_, v___x_1407_, v___y_1403_, v___y_1405_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object* v_declName_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(v_declName_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1415_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0));
v___x_1418_ = l_Lean_stringToMessageData(v___x_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object* v_constName_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; lean_object* v_env_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_st_ref_get(v___y_1423_);
v_env_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc_ref(v_env_1426_);
lean_dec(v___x_1425_);
lean_inc(v_constName_1419_);
v___x_1427_ = l_Lean_isInductiveCore_x3f(v_env_1426_, v_constName_1419_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v___x_1428_; uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1428_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_1429_ = 0;
v___x_1430_ = l_Lean_MessageData_ofConstName(v_constName_1419_, v___x_1429_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1428_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_1433_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
return v___x_1434_;
}
else
{
lean_object* v_val_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_constName_1419_);
v_val_1435_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1427_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_val_1435_);
lean_dec(v___x_1427_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 0);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_val_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object* v_constName_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(v_constName_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(lean_object* v_ref_1450_, lean_object* v_msg_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_fileName_1457_; lean_object* v_fileMap_1458_; lean_object* v_options_1459_; lean_object* v_currRecDepth_1460_; lean_object* v_maxRecDepth_1461_; lean_object* v_ref_1462_; lean_object* v_currNamespace_1463_; lean_object* v_openDecls_1464_; lean_object* v_initHeartbeats_1465_; lean_object* v_maxHeartbeats_1466_; lean_object* v_quotContext_1467_; lean_object* v_currMacroScope_1468_; uint8_t v_diag_1469_; lean_object* v_cancelTk_x3f_1470_; uint8_t v_suppressElabErrors_1471_; lean_object* v_inheritedTraceOptions_1472_; lean_object* v_ref_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_fileName_1457_ = lean_ctor_get(v___y_1454_, 0);
v_fileMap_1458_ = lean_ctor_get(v___y_1454_, 1);
v_options_1459_ = lean_ctor_get(v___y_1454_, 2);
v_currRecDepth_1460_ = lean_ctor_get(v___y_1454_, 3);
v_maxRecDepth_1461_ = lean_ctor_get(v___y_1454_, 4);
v_ref_1462_ = lean_ctor_get(v___y_1454_, 5);
v_currNamespace_1463_ = lean_ctor_get(v___y_1454_, 6);
v_openDecls_1464_ = lean_ctor_get(v___y_1454_, 7);
v_initHeartbeats_1465_ = lean_ctor_get(v___y_1454_, 8);
v_maxHeartbeats_1466_ = lean_ctor_get(v___y_1454_, 9);
v_quotContext_1467_ = lean_ctor_get(v___y_1454_, 10);
v_currMacroScope_1468_ = lean_ctor_get(v___y_1454_, 11);
v_diag_1469_ = lean_ctor_get_uint8(v___y_1454_, sizeof(void*)*14);
v_cancelTk_x3f_1470_ = lean_ctor_get(v___y_1454_, 12);
v_suppressElabErrors_1471_ = lean_ctor_get_uint8(v___y_1454_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1472_ = lean_ctor_get(v___y_1454_, 13);
v_ref_1473_ = l_Lean_replaceRef(v_ref_1450_, v_ref_1462_);
lean_inc_ref(v_inheritedTraceOptions_1472_);
lean_inc(v_cancelTk_x3f_1470_);
lean_inc(v_currMacroScope_1468_);
lean_inc(v_quotContext_1467_);
lean_inc(v_maxHeartbeats_1466_);
lean_inc(v_initHeartbeats_1465_);
lean_inc(v_openDecls_1464_);
lean_inc(v_currNamespace_1463_);
lean_inc(v_maxRecDepth_1461_);
lean_inc(v_currRecDepth_1460_);
lean_inc_ref(v_options_1459_);
lean_inc_ref(v_fileMap_1458_);
lean_inc_ref(v_fileName_1457_);
v___x_1474_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1474_, 0, v_fileName_1457_);
lean_ctor_set(v___x_1474_, 1, v_fileMap_1458_);
lean_ctor_set(v___x_1474_, 2, v_options_1459_);
lean_ctor_set(v___x_1474_, 3, v_currRecDepth_1460_);
lean_ctor_set(v___x_1474_, 4, v_maxRecDepth_1461_);
lean_ctor_set(v___x_1474_, 5, v_ref_1473_);
lean_ctor_set(v___x_1474_, 6, v_currNamespace_1463_);
lean_ctor_set(v___x_1474_, 7, v_openDecls_1464_);
lean_ctor_set(v___x_1474_, 8, v_initHeartbeats_1465_);
lean_ctor_set(v___x_1474_, 9, v_maxHeartbeats_1466_);
lean_ctor_set(v___x_1474_, 10, v_quotContext_1467_);
lean_ctor_set(v___x_1474_, 11, v_currMacroScope_1468_);
lean_ctor_set(v___x_1474_, 12, v_cancelTk_x3f_1470_);
lean_ctor_set(v___x_1474_, 13, v_inheritedTraceOptions_1472_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*14, v_diag_1469_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*14 + 1, v_suppressElabErrors_1471_);
v___x_1475_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_1451_, v___y_1452_, v___y_1453_, v___x_1474_, v___y_1455_);
lean_dec_ref_known(v___x_1474_, 14);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg___boxed(lean_object* v_ref_1476_, lean_object* v_msg_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_1476_, v_msg_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v_ref_1476_);
return v_res_1483_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0(void){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
lean_ctor_set(v___x_1489_, 2, v___x_1488_);
lean_ctor_set(v___x_1489_, 3, v___x_1488_);
lean_ctor_set(v___x_1489_, 4, v___x_1487_);
lean_ctor_set(v___x_1489_, 5, v___x_1487_);
lean_ctor_set(v___x_1489_, 6, v___x_1487_);
lean_ctor_set(v___x_1489_, 7, v___x_1487_);
lean_ctor_set(v___x_1489_, 8, v___x_1487_);
lean_ctor_set(v___x_1489_, 9, v___x_1487_);
lean_ctor_set(v___x_1489_, 10, v___x_1487_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_unsigned_to_nat(32u);
v___x_1491_ = lean_mk_empty_array_with_capacity(v___x_1490_);
v___x_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4(void){
_start:
{
size_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1493_ = ((size_t)5ULL);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_unsigned_to_nat(32u);
v___x_1496_ = lean_mk_empty_array_with_capacity(v___x_1495_);
v___x_1497_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3);
v___x_1498_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v___x_1496_);
lean_ctor_set(v___x_1498_, 2, v___x_1494_);
lean_ctor_set(v___x_1498_, 3, v___x_1494_);
lean_ctor_set_usize(v___x_1498_, 4, v___x_1493_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1499_ = lean_box(1);
v___x_1500_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4);
v___x_1501_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1);
v___x_1502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v___x_1500_);
lean_ctor_set(v___x_1502_, 2, v___x_1499_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6));
v___x_1505_ = l_Lean_stringToMessageData(v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8));
v___x_1508_ = l_Lean_stringToMessageData(v___x_1507_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10));
v___x_1511_ = l_Lean_stringToMessageData(v___x_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12));
v___x_1514_ = l_Lean_stringToMessageData(v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16));
v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18));
v___x_1523_ = l_Lean_stringToMessageData(v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(lean_object* v_msg_1524_, lean_object* v_declHint_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v_env_1529_; uint8_t v___x_1530_; 
v___x_1528_ = lean_st_ref_get(v___y_1526_);
v_env_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc_ref(v_env_1529_);
lean_dec(v___x_1528_);
v___x_1530_ = l_Lean_Name_isAnonymous(v_declHint_1525_);
if (v___x_1530_ == 0)
{
uint8_t v_isExporting_1531_; 
v_isExporting_1531_ = lean_ctor_get_uint8(v_env_1529_, sizeof(void*)*8);
if (v_isExporting_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_dec_ref(v_env_1529_);
lean_dec(v_declHint_1525_);
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_msg_1524_);
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
lean_inc_ref(v_env_1529_);
v___x_1533_ = l_Lean_Environment_setExporting(v_env_1529_, v___x_1530_);
lean_inc(v_declHint_1525_);
lean_inc_ref(v___x_1533_);
v___x_1534_ = l_Lean_Environment_contains(v___x_1533_, v_declHint_1525_, v_isExporting_1531_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_dec_ref(v___x_1533_);
lean_dec_ref(v_env_1529_);
lean_dec(v_declHint_1525_);
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_msg_1524_);
return v___x_1535_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v_c_1541_; lean_object* v___x_1542_; 
v___x_1536_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2);
v___x_1537_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5);
v___x_1538_ = l_Lean_Options_empty;
v___x_1539_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1533_);
lean_ctor_set(v___x_1539_, 1, v___x_1536_);
lean_ctor_set(v___x_1539_, 2, v___x_1537_);
lean_ctor_set(v___x_1539_, 3, v___x_1538_);
lean_inc(v_declHint_1525_);
v___x_1540_ = l_Lean_MessageData_ofConstName(v_declHint_1525_, v___x_1530_);
v_c_1541_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1541_, 0, v___x_1539_);
lean_ctor_set(v_c_1541_, 1, v___x_1540_);
v___x_1542_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1529_, v_declHint_1525_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec_ref(v_env_1529_);
lean_dec(v_declHint_1525_);
v___x_1543_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v_c_1541_);
v___x_1545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = l_Lean_MessageData_note(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_msg_1524_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
else
{
lean_object* v_val_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1585_; 
v_val_1550_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1552_ = v___x_1542_;
v_isShared_1553_ = v_isSharedCheck_1585_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_val_1550_);
lean_dec(v___x_1542_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1585_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v_mod_1557_; uint8_t v___x_1558_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = l_Lean_Environment_header(v_env_1529_);
lean_dec_ref(v_env_1529_);
v___x_1556_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1555_);
v_mod_1557_ = lean_array_get(v___x_1554_, v___x_1556_, v_val_1550_);
lean_dec(v_val_1550_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = l_Lean_isPrivateName(v_declHint_1525_);
lean_dec(v_declHint_1525_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1559_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v_c_1541_);
v___x_1561_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_MessageData_ofName(v_mod_1557_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = l_Lean_MessageData_note(v___x_1566_);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v_msg_1524_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set_tag(v___x_1552_, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1568_);
v___x_1570_ = v___x_1552_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1572_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v_c_1541_);
v___x_1574_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = l_Lean_MessageData_ofName(v_mod_1557_);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = l_Lean_MessageData_note(v___x_1579_);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v_msg_1524_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set_tag(v___x_1552_, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1581_);
v___x_1583_ = v___x_1552_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1586_; 
lean_dec_ref(v_env_1529_);
lean_dec(v_declHint_1525_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_msg_1524_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___boxed(lean_object* v_msg_1587_, lean_object* v_declHint_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_1587_, v_declHint_1588_, v___y_1589_);
lean_dec(v___y_1589_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(lean_object* v_msg_1592_, lean_object* v_declHint_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1609_; 
v___x_1599_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_1592_, v_declHint_1593_, v___y_1597_);
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1609_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1609_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1604_ = l_Lean_unknownIdentifierMessageTag;
v___x_1605_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
lean_ctor_set(v___x_1605_, 1, v_a_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1605_);
v___x_1607_ = v___x_1602_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32___boxed(lean_object* v_msg_1610_, lean_object* v_declHint_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(v_msg_1610_, v_declHint_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(lean_object* v_ref_1618_, lean_object* v_msg_1619_, lean_object* v_declHint_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; lean_object* v_a_1627_; lean_object* v___x_1628_; 
v___x_1626_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(v_msg_1619_, v_declHint_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_1618_, v_a_1627_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg___boxed(lean_object* v_ref_1629_, lean_object* v_msg_1630_, lean_object* v_declHint_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_1629_, v_msg_1630_, v_declHint_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v_ref_1629_);
return v_res_1637_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0));
v___x_1640_ = l_Lean_stringToMessageData(v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(lean_object* v_ref_1641_, lean_object* v_constName_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1648_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1);
v___x_1649_ = 0;
lean_inc(v_constName_1642_);
v___x_1650_ = l_Lean_MessageData_ofConstName(v_constName_1642_, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1648_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_1641_, v___x_1653_, v_constName_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___boxed(lean_object* v_ref_1655_, lean_object* v_constName_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_1655_, v_constName_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v_ref_1655_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(lean_object* v_constName_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_ref_1669_; lean_object* v___x_1670_; 
v_ref_1669_ = lean_ctor_get(v___y_1666_, 5);
v___x_1670_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_1669_, v_constName_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg___boxed(lean_object* v_constName_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object* v_constName_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v_env_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; 
v___x_1684_ = lean_st_ref_get(v___y_1682_);
v_env_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc_ref(v_env_1685_);
lean_dec(v___x_1684_);
v___x_1686_ = 0;
lean_inc(v_constName_1678_);
v___x_1687_ = l_Lean_Environment_find_x3f(v_env_1685_, v_constName_1678_, v___x_1686_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1688_;
}
else
{
lean_object* v_val_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_constName_1678_);
v_val_1689_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1687_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_val_1689_);
lean_dec(v___x_1687_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set_tag(v___x_1691_, 0);
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_val_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object* v_constName_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_constName_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(lean_object* v_keys_1704_, lean_object* v_vals_1705_, lean_object* v_i_1706_, lean_object* v_k_1707_){
_start:
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_array_get_size(v_keys_1704_);
v___x_1709_ = lean_nat_dec_lt(v_i_1706_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
lean_dec(v_i_1706_);
v___x_1710_ = lean_box(0);
return v___x_1710_;
}
else
{
lean_object* v_k_x27_1711_; uint8_t v___x_1712_; 
v_k_x27_1711_ = lean_array_fget_borrowed(v_keys_1704_, v_i_1706_);
v___x_1712_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_k_1707_, v_k_x27_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_nat_add(v_i_1706_, v___x_1713_);
lean_dec(v_i_1706_);
v_i_1706_ = v___x_1714_;
goto _start;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_array_fget_borrowed(v_vals_1705_, v_i_1706_);
lean_dec(v_i_1706_);
lean_inc(v___x_1716_);
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg___boxed(lean_object* v_keys_1718_, lean_object* v_vals_1719_, lean_object* v_i_1720_, lean_object* v_k_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_keys_1718_, v_vals_1719_, v_i_1720_, v_k_1721_);
lean_dec_ref(v_k_1721_);
lean_dec_ref(v_vals_1719_);
lean_dec_ref(v_keys_1718_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object* v_x_1723_, size_t v_x_1724_, lean_object* v_x_1725_){
_start:
{
if (lean_obj_tag(v_x_1723_) == 0)
{
lean_object* v_es_1726_; lean_object* v___x_1727_; size_t v___x_1728_; size_t v___x_1729_; lean_object* v_j_1730_; lean_object* v___x_1731_; 
v_es_1726_ = lean_ctor_get(v_x_1723_, 0);
v___x_1727_ = lean_box(2);
v___x_1728_ = ((size_t)31ULL);
v___x_1729_ = lean_usize_land(v_x_1724_, v___x_1728_);
v_j_1730_ = lean_usize_to_nat(v___x_1729_);
v___x_1731_ = lean_array_get_borrowed(v___x_1727_, v_es_1726_, v_j_1730_);
lean_dec(v_j_1730_);
switch(lean_obj_tag(v___x_1731_))
{
case 0:
{
lean_object* v_key_1732_; lean_object* v_val_1733_; uint8_t v___x_1734_; 
v_key_1732_ = lean_ctor_get(v___x_1731_, 0);
v_val_1733_ = lean_ctor_get(v___x_1731_, 1);
v___x_1734_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_1725_, v_key_1732_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_box(0);
return v___x_1735_;
}
else
{
lean_object* v___x_1736_; 
lean_inc(v_val_1733_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_val_1733_);
return v___x_1736_;
}
}
case 1:
{
lean_object* v_node_1737_; size_t v___x_1738_; size_t v___x_1739_; 
v_node_1737_ = lean_ctor_get(v___x_1731_, 0);
v___x_1738_ = ((size_t)5ULL);
v___x_1739_ = lean_usize_shift_right(v_x_1724_, v___x_1738_);
v_x_1723_ = v_node_1737_;
v_x_1724_ = v___x_1739_;
goto _start;
}
default: 
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_box(0);
return v___x_1741_;
}
}
}
else
{
lean_object* v_ks_1742_; lean_object* v_vs_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_ks_1742_ = lean_ctor_get(v_x_1723_, 0);
v_vs_1743_ = lean_ctor_get(v_x_1723_, 1);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_ks_1742_, v_vs_1743_, v___x_1744_, v_x_1725_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_x_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
size_t v_x_23035__boxed_1749_; lean_object* v_res_1750_; 
v_x_23035__boxed_1749_ = lean_unbox_usize(v_x_1747_);
lean_dec(v_x_1747_);
v_res_1750_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_1746_, v_x_23035__boxed_1749_, v_x_1748_);
lean_dec_ref(v_x_1748_);
lean_dec_ref(v_x_1746_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
uint64_t v___x_1753_; size_t v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_1752_);
v___x_1754_ = lean_uint64_to_usize(v___x_1753_);
v___x_1755_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_1751_, v___x_1754_, v_x_1752_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object* v_x_1756_, lean_object* v_x_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_1756_, v_x_1757_);
lean_dec_ref(v_x_1757_);
lean_dec_ref(v_x_1756_);
return v_res_1758_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__2(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1761_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6));
v___x_1762_ = lean_unsigned_to_nat(42u);
v___x_1763_ = lean_unsigned_to_nat(81u);
v___x_1764_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__1));
v___x_1765_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__0));
v___x_1766_ = l_mkPanicMessageWithDecl(v___x_1765_, v___x_1764_, v___x_1763_, v___x_1762_, v___x_1761_);
return v___x_1766_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__4(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__3));
v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__5(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0));
v___x_1771_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0));
v___x_1772_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1771_, v___x_1770_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__9(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__8));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object* v_indName_1779_, lean_object* v_ctors_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1786_; lean_object* v_env_1787_; lean_object* v___x_1788_; uint8_t v_isModule_1789_; lean_object* v___x_1790_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___x_2035_; uint8_t v___y_2037_; 
v___x_1786_ = lean_st_ref_get(v_a_1784_);
v_env_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc_ref(v_env_1787_);
lean_dec(v___x_1786_);
v___x_1788_ = l_Lean_Environment_header(v_env_1787_);
v_isModule_1789_ = lean_ctor_get_uint8(v___x_1788_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1788_);
v___x_1790_ = l_Lean_instInhabitedExpr;
v___x_2035_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__5, &l_Lean_Meta_mkSparseCasesOn___closed__5_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__5);
if (v_isModule_1789_ == 0)
{
v___y_2037_ = v_isModule_1789_;
goto v___jp_2036_;
}
else
{
uint8_t v_isExporting_2094_; 
v_isExporting_2094_ = lean_ctor_get_uint8(v_env_1787_, sizeof(void*)*8);
if (v_isExporting_2094_ == 0)
{
v___y_2037_ = v_isModule_1789_;
goto v___jp_2036_;
}
else
{
uint8_t v___x_2095_; 
v___x_2095_ = 0;
v___y_2037_ = v___x_2095_;
goto v___jp_2036_;
}
}
v___jp_1791_:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_ConstantInfo_levelParams(v___y_1798_);
if (lean_obj_tag(v___x_1809_) == 1)
{
lean_object* v_tail_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; lean_object* v___x_1816_; 
v_tail_1810_ = lean_ctor_get(v___x_1809_, 1);
lean_inc(v_tail_1810_);
v___x_1811_ = lean_box(0);
v___x_1812_ = l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(v_tail_1810_, v___x_1811_);
lean_inc_ref(v_ctors_1780_);
v___f_1813_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__2___boxed), 16, 9);
lean_closure_set(v___f_1813_, 0, v___y_1793_);
lean_closure_set(v___f_1813_, 1, v___x_1790_);
lean_closure_set(v___f_1813_, 2, v___y_1795_);
lean_closure_set(v___f_1813_, 3, v_ctors_1780_);
lean_closure_set(v___f_1813_, 4, v___y_1794_);
lean_closure_set(v___f_1813_, 5, v___x_1812_);
lean_closure_set(v___f_1813_, 6, v___y_1792_);
lean_closure_set(v___f_1813_, 7, v___y_1797_);
lean_closure_set(v___f_1813_, 8, v___y_1796_);
v___x_1814_ = l_Lean_ConstantInfo_type(v___y_1798_);
lean_dec_ref(v___y_1798_);
v___x_1815_ = 0;
v___x_1816_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v___x_1814_, v___f_1813_, v___x_1815_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1818_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc_n(v_a_1817_, 2);
lean_dec_ref_known(v___x_1816_, 1);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1806_);
lean_inc_ref(v___y_1805_);
v___x_1818_ = lean_infer_type(v_a_1817_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1968_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v___x_1820_ = lean_box(1);
lean_inc(v___y_1804_);
v___x_1821_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___y_1804_, v___x_1809_, v_a_1819_, v_a_1817_, v___x_1820_, v___y_1808_);
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1968_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1968_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 1);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_addDecl(v___x_1827_, v___x_1815_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v___x_1829_; lean_object* v_env_1830_; lean_object* v_nextMacroScope_1831_; lean_object* v_ngen_1832_; lean_object* v_auxDeclNGen_1833_; lean_object* v_traceState_1834_; lean_object* v_messages_1835_; lean_object* v_infoState_1836_; lean_object* v_snapshotTasks_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref_known(v___x_1828_, 1);
v___x_1829_ = lean_st_ref_take(v___y_1808_);
v_env_1830_ = lean_ctor_get(v___x_1829_, 0);
v_nextMacroScope_1831_ = lean_ctor_get(v___x_1829_, 1);
v_ngen_1832_ = lean_ctor_get(v___x_1829_, 2);
v_auxDeclNGen_1833_ = lean_ctor_get(v___x_1829_, 3);
v_traceState_1834_ = lean_ctor_get(v___x_1829_, 4);
v_messages_1835_ = lean_ctor_get(v___x_1829_, 6);
v_infoState_1836_ = lean_ctor_get(v___x_1829_, 7);
v_snapshotTasks_1837_ = lean_ctor_get(v___x_1829_, 8);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; 
v_unused_1958_ = lean_ctor_get(v___x_1829_, 5);
lean_dec(v_unused_1958_);
v___x_1839_ = v___x_1829_;
v_isShared_1840_ = v_isSharedCheck_1957_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_snapshotTasks_1837_);
lean_inc(v_infoState_1836_);
lean_inc(v_messages_1835_);
lean_inc(v_traceState_1834_);
lean_inc(v_auxDeclNGen_1833_);
lean_inc(v_ngen_1832_);
lean_inc(v_nextMacroScope_1831_);
lean_inc(v_env_1830_);
lean_dec(v___x_1829_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1957_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
lean_inc_ref(v___y_1803_);
v___x_1841_ = l_Lean_EnvExtension_modifyState___redArg(v___y_1803_, v_env_1830_, v___y_1801_, v___y_1799_, v___y_1800_);
v___x_1842_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 5, v___x_1842_);
lean_ctor_set(v___x_1839_, 0, v___x_1841_);
v___x_1844_ = v___x_1839_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_nextMacroScope_1831_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v_ngen_1832_);
lean_ctor_set(v_reuseFailAlloc_1956_, 3, v_auxDeclNGen_1833_);
lean_ctor_set(v_reuseFailAlloc_1956_, 4, v_traceState_1834_);
lean_ctor_set(v_reuseFailAlloc_1956_, 5, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1956_, 6, v_messages_1835_);
lean_ctor_set(v_reuseFailAlloc_1956_, 7, v_infoState_1836_);
lean_ctor_set(v_reuseFailAlloc_1956_, 8, v_snapshotTasks_1837_);
v___x_1844_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v_mctx_1847_; lean_object* v_zetaDeltaFVarIds_1848_; lean_object* v_postponed_1849_; lean_object* v_diag_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1954_; 
v___x_1845_ = lean_st_ref_put(v___y_1808_, v___x_1844_);
v___x_1846_ = lean_st_ref_take(v___y_1806_);
v_mctx_1847_ = lean_ctor_get(v___x_1846_, 0);
v_zetaDeltaFVarIds_1848_ = lean_ctor_get(v___x_1846_, 2);
v_postponed_1849_ = lean_ctor_get(v___x_1846_, 3);
v_diag_1850_ = lean_ctor_get(v___x_1846_, 4);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v___x_1846_, 1);
lean_dec(v_unused_1955_);
v___x_1852_ = v___x_1846_;
v_isShared_1853_ = v_isSharedCheck_1954_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_diag_1850_);
lean_inc(v_postponed_1849_);
lean_inc(v_zetaDeltaFVarIds_1848_);
lean_inc(v_mctx_1847_);
lean_dec(v___x_1846_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1954_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v___x_1854_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_mctx_1847_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v_zetaDeltaFVarIds_1848_);
lean_ctor_set(v_reuseFailAlloc_1953_, 3, v_postponed_1849_);
lean_ctor_set(v_reuseFailAlloc_1953_, 4, v_diag_1850_);
v___x_1856_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_env_1860_; lean_object* v_nextMacroScope_1861_; lean_object* v_ngen_1862_; lean_object* v_auxDeclNGen_1863_; lean_object* v_traceState_1864_; lean_object* v_messages_1865_; lean_object* v_infoState_1866_; lean_object* v_snapshotTasks_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1951_; 
v___x_1857_ = lean_st_ref_put(v___y_1806_, v___x_1856_);
lean_inc(v___y_1804_);
v___x_1858_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec_ref(v___x_1858_);
v___x_1859_ = lean_st_ref_take(v___y_1808_);
v_env_1860_ = lean_ctor_get(v___x_1859_, 0);
v_nextMacroScope_1861_ = lean_ctor_get(v___x_1859_, 1);
v_ngen_1862_ = lean_ctor_get(v___x_1859_, 2);
v_auxDeclNGen_1863_ = lean_ctor_get(v___x_1859_, 3);
v_traceState_1864_ = lean_ctor_get(v___x_1859_, 4);
v_messages_1865_ = lean_ctor_get(v___x_1859_, 6);
v_infoState_1866_ = lean_ctor_get(v___x_1859_, 7);
v_snapshotTasks_1867_ = lean_ctor_get(v___x_1859_, 8);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v___x_1859_, 5);
lean_dec(v_unused_1952_);
v___x_1869_ = v___x_1859_;
v_isShared_1870_ = v_isSharedCheck_1951_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_snapshotTasks_1867_);
lean_inc(v_infoState_1866_);
lean_inc(v_messages_1865_);
lean_inc(v_traceState_1864_);
lean_inc(v_auxDeclNGen_1863_);
lean_inc(v_ngen_1862_);
lean_inc(v_nextMacroScope_1861_);
lean_inc(v_env_1860_);
lean_dec(v___x_1859_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1951_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
lean_inc(v___y_1804_);
v___x_1871_ = l_Lean_markSparseCasesOn(v_env_1860_, v___y_1804_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 5, v___x_1842_);
lean_ctor_set(v___x_1869_, 0, v___x_1871_);
v___x_1873_ = v___x_1869_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_nextMacroScope_1861_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_ngen_1862_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_auxDeclNGen_1863_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v_traceState_1864_);
lean_ctor_set(v_reuseFailAlloc_1950_, 5, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1950_, 6, v_messages_1865_);
lean_ctor_set(v_reuseFailAlloc_1950_, 7, v_infoState_1866_);
lean_ctor_set(v_reuseFailAlloc_1950_, 8, v_snapshotTasks_1867_);
v___x_1873_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_mctx_1876_; lean_object* v_zetaDeltaFVarIds_1877_; lean_object* v_postponed_1878_; lean_object* v_diag_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1948_; 
v___x_1874_ = lean_st_ref_put(v___y_1808_, v___x_1873_);
v___x_1875_ = lean_st_ref_take(v___y_1806_);
v_mctx_1876_ = lean_ctor_get(v___x_1875_, 0);
v_zetaDeltaFVarIds_1877_ = lean_ctor_get(v___x_1875_, 2);
v_postponed_1878_ = lean_ctor_get(v___x_1875_, 3);
v_diag_1879_ = lean_ctor_get(v___x_1875_, 4);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1948_ == 0)
{
lean_object* v_unused_1949_; 
v_unused_1949_ = lean_ctor_get(v___x_1875_, 1);
lean_dec(v_unused_1949_);
v___x_1881_ = v___x_1875_;
v_isShared_1882_ = v_isSharedCheck_1948_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_diag_1879_);
lean_inc(v_postponed_1878_);
lean_inc(v_zetaDeltaFVarIds_1877_);
lean_inc(v_mctx_1876_);
lean_dec(v___x_1875_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1948_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 1, v___x_1854_);
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_mctx_1876_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_zetaDeltaFVarIds_1877_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_postponed_1878_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_diag_1879_);
v___x_1884_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v_env_1887_; lean_object* v_nextMacroScope_1888_; lean_object* v_ngen_1889_; lean_object* v_auxDeclNGen_1890_; lean_object* v_traceState_1891_; lean_object* v_messages_1892_; lean_object* v_infoState_1893_; lean_object* v_snapshotTasks_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1945_; 
v___x_1885_ = lean_st_ref_put(v___y_1806_, v___x_1884_);
v___x_1886_ = lean_st_ref_take(v___y_1808_);
v_env_1887_ = lean_ctor_get(v___x_1886_, 0);
v_nextMacroScope_1888_ = lean_ctor_get(v___x_1886_, 1);
v_ngen_1889_ = lean_ctor_get(v___x_1886_, 2);
v_auxDeclNGen_1890_ = lean_ctor_get(v___x_1886_, 3);
v_traceState_1891_ = lean_ctor_get(v___x_1886_, 4);
v_messages_1892_ = lean_ctor_get(v___x_1886_, 6);
v_infoState_1893_ = lean_ctor_get(v___x_1886_, 7);
v_snapshotTasks_1894_ = lean_ctor_get(v___x_1886_, 8);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1886_, 5);
lean_dec(v_unused_1946_);
v___x_1896_ = v___x_1886_;
v_isShared_1897_ = v_isSharedCheck_1945_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_snapshotTasks_1894_);
lean_inc(v_infoState_1893_);
lean_inc(v_messages_1892_);
lean_inc(v_traceState_1891_);
lean_inc(v_auxDeclNGen_1890_);
lean_inc(v_ngen_1889_);
lean_inc(v_nextMacroScope_1888_);
lean_inc(v_env_1887_);
lean_dec(v___x_1886_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1945_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_numParams_1898_; lean_object* v_numIndices_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v_numParams_1898_ = lean_ctor_get(v___y_1802_, 1);
lean_inc(v_numParams_1898_);
v_numIndices_1899_ = lean_ctor_get(v___y_1802_, 2);
lean_inc(v_numIndices_1899_);
lean_dec_ref(v___y_1802_);
v___x_1900_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v___x_1901_ = lean_unsigned_to_nat(1u);
v___x_1902_ = lean_nat_add(v_numParams_1898_, v___x_1901_);
lean_dec(v_numParams_1898_);
v___x_1903_ = lean_nat_add(v___x_1902_, v_numIndices_1899_);
lean_dec(v_numIndices_1899_);
lean_dec(v___x_1902_);
v___x_1904_ = lean_nat_add(v___x_1903_, v___x_1901_);
v___x_1905_ = lean_array_get_size(v_ctors_1780_);
v___x_1906_ = lean_nat_add(v___x_1904_, v___x_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_nat_add(v___x_1906_, v___x_1901_);
lean_dec(v___x_1906_);
v___x_1908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1908_, 0, v_indName_1779_);
lean_ctor_set(v___x_1908_, 1, v___x_1903_);
lean_ctor_set(v___x_1908_, 2, v___x_1907_);
lean_ctor_set(v___x_1908_, 3, v_ctors_1780_);
lean_inc(v___y_1804_);
v___x_1909_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1900_, v_env_1887_, v___y_1804_, v___x_1908_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 5, v___x_1842_);
lean_ctor_set(v___x_1896_, 0, v___x_1909_);
v___x_1911_ = v___x_1896_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_nextMacroScope_1888_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_ngen_1889_);
lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_auxDeclNGen_1890_);
lean_ctor_set(v_reuseFailAlloc_1944_, 4, v_traceState_1891_);
lean_ctor_set(v_reuseFailAlloc_1944_, 5, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1944_, 6, v_messages_1892_);
lean_ctor_set(v_reuseFailAlloc_1944_, 7, v_infoState_1893_);
lean_ctor_set(v_reuseFailAlloc_1944_, 8, v_snapshotTasks_1894_);
v___x_1911_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v_mctx_1914_; lean_object* v_zetaDeltaFVarIds_1915_; lean_object* v_postponed_1916_; lean_object* v_diag_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1942_; 
v___x_1912_ = lean_st_ref_put(v___y_1808_, v___x_1911_);
v___x_1913_ = lean_st_ref_take(v___y_1806_);
v_mctx_1914_ = lean_ctor_get(v___x_1913_, 0);
v_zetaDeltaFVarIds_1915_ = lean_ctor_get(v___x_1913_, 2);
v_postponed_1916_ = lean_ctor_get(v___x_1913_, 3);
v_diag_1917_ = lean_ctor_get(v___x_1913_, 4);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v___x_1913_, 1);
lean_dec(v_unused_1943_);
v___x_1919_ = v___x_1913_;
v_isShared_1920_ = v_isSharedCheck_1942_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_diag_1917_);
lean_inc(v_postponed_1916_);
lean_inc(v_zetaDeltaFVarIds_1915_);
lean_inc(v_mctx_1914_);
lean_dec(v___x_1913_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1942_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_1854_);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_mctx_1914_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_zetaDeltaFVarIds_1915_);
lean_ctor_set(v_reuseFailAlloc_1941_, 3, v_postponed_1916_);
lean_ctor_set(v_reuseFailAlloc_1941_, 4, v_diag_1917_);
v___x_1922_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_st_ref_put(v___y_1806_, v___x_1922_);
lean_inc(v___y_1804_);
v___x_1924_ = l_Lean_enableRealizationsForConst(v___y_1804_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v___x_1924_, 0);
lean_dec(v_unused_1932_);
v___x_1926_ = v___x_1924_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_dec(v___x_1924_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___y_1804_);
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___y_1804_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v___y_1804_);
v_a_1933_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1924_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1924_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
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
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v_ctors_1780_);
lean_dec(v_indName_1779_);
v_a_1959_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1828_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1828_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v_a_1817_);
lean_dec_ref_known(v___x_1809_, 2);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v_ctors_1780_);
lean_dec(v_indName_1779_);
v_a_1969_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1818_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1818_);
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
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref_known(v___x_1809_, 2);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v_ctors_1780_);
lean_dec(v_indName_1779_);
v_a_1977_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1816_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1816_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec(v___x_1809_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v_ctors_1780_);
lean_dec(v_indName_1779_);
v___x_1985_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__2, &l_Lean_Meta_mkSparseCasesOn___closed__2_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__2);
v___x_1986_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(v___x_1985_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
return v___x_1986_;
}
}
v___jp_1987_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_inc(v_indName_1779_);
v___x_2001_ = l_Lean_mkCasesOnName(v_indName_1779_);
lean_inc(v___x_2001_);
v___x_2002_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(v___x_2001_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_toConstantVal_2003_; lean_object* v_a_2004_; lean_object* v_levelParams_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_toConstantVal_2003_ = lean_ctor_get(v___y_1994_, 0);
v_a_2004_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2002_, 1);
v_levelParams_2005_ = lean_ctor_get(v_toConstantVal_2003_, 1);
lean_inc(v_indName_1779_);
v___x_2006_ = l_Lean_mkCtorIdxName(v_indName_1779_);
v___x_2007_ = l_Lean_ConstantInfo_levelParams(v_a_2004_);
v___x_2008_ = l_List_lengthTR___redArg(v___x_2007_);
lean_dec(v___x_2007_);
v___x_2009_ = l_List_lengthTR___redArg(v_levelParams_2005_);
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_nat_add(v___x_2009_, v___x_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_nat_dec_eq(v___x_2008_, v___x_2011_);
lean_dec(v___x_2011_);
lean_dec(v___x_2008_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v___x_2006_);
lean_dec(v_a_2004_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v_ctors_1780_);
lean_dec(v_indName_1779_);
v___x_2013_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__4, &l_Lean_Meta_mkSparseCasesOn___closed__4_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__4);
v___x_2014_ = l_Lean_MessageData_ofConstName(v___x_2001_, v___x_2012_);
v___x_2015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_2017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_2017_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
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
else
{
lean_inc(v_a_2004_);
v___y_1792_ = v_a_2004_;
v___y_1793_ = v___y_1988_;
v___y_1794_ = v___x_2006_;
v___y_1795_ = v___y_1989_;
v___y_1796_ = v___x_2001_;
v___y_1797_ = v___y_1991_;
v___y_1798_ = v_a_2004_;
v___y_1799_ = v___y_1992_;
v___y_1800_ = v___y_1993_;
v___y_1801_ = v___y_1990_;
v___y_1802_ = v___y_1994_;
v___y_1803_ = v___y_1995_;
v___y_1804_ = v___y_1996_;
v___y_1805_ = v___y_1997_;
v___y_1806_ = v___y_1998_;
v___y_1807_ = v___y_1999_;
v___y_1808_ = v___y_2000_;
goto v___jp_1791_;
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v___x_2001_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v_ctors_1780_);
lean_dec(v_indName_1779_);
v_a_2027_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2002_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2002_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
v___jp_2036_:
{
lean_object* v___x_2038_; lean_object* v_asyncMode_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2038_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
v_asyncMode_2039_ = lean_ctor_get(v___x_2038_, 2);
lean_inc_ref(v_ctors_1780_);
lean_inc(v_indName_1779_);
v___x_2040_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2040_, 0, v_indName_1779_);
lean_ctor_set(v___x_2040_, 1, v_ctors_1780_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*2, v___y_2037_);
v___x_2041_ = lean_box(0);
v___x_2042_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2035_, v___x_2038_, v_env_1787_, v_asyncMode_2039_, v___x_2041_);
v___x_2043_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v___x_2042_, v___x_2040_);
lean_dec(v___x_2042_);
if (lean_obj_tag(v___x_2043_) == 1)
{
lean_object* v_val_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref_known(v___x_2040_, 2);
lean_dec_ref(v_ctors_1780_);
lean_dec(v_indName_1779_);
v_val_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_val_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 0);
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_val_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_a_2054_; lean_object* v___x_2055_; 
lean_dec(v___x_2043_);
v___x_2052_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__7));
v___x_2053_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v___x_2052_, v_a_1784_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
lean_inc(v_indName_1779_);
v___x_2055_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(v_indName_1779_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; size_t v_sz_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = lean_box(0);
v_sz_2058_ = lean_array_size(v_ctors_1780_);
v___x_2059_ = ((size_t)0ULL);
lean_inc(v_indName_1779_);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_2056_, v_indName_1779_, v_ctors_1780_, v_sz_2058_, v___x_2059_, v___x_2057_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_numParams_2061_; lean_object* v_numIndices_2062_; lean_object* v_ctors_2063_; lean_object* v___f_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
lean_dec_ref_known(v___x_2060_, 1);
v_numParams_2061_ = lean_ctor_get(v_a_2056_, 1);
lean_inc(v_numParams_2061_);
v_numIndices_2062_ = lean_ctor_get(v_a_2056_, 2);
lean_inc(v_numIndices_2062_);
v_ctors_2063_ = lean_ctor_get(v_a_2056_, 4);
lean_inc(v_ctors_2063_);
lean_inc(v_a_2054_);
v___f_2064_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__0), 3, 2);
lean_closure_set(v___f_2064_, 0, v___x_2040_);
lean_closure_set(v___f_2064_, 1, v_a_2054_);
v___x_2065_ = lean_array_get_size(v_ctors_1780_);
v___x_2066_ = l_List_lengthTR___redArg(v_ctors_2063_);
v___x_2067_ = lean_nat_dec_eq(v___x_2065_, v___x_2066_);
lean_dec(v___x_2066_);
if (v___x_2067_ == 0)
{
v___y_1988_ = v_numParams_2061_;
v___y_1989_ = v_numIndices_2062_;
v___y_1990_ = v___f_2064_;
v___y_1991_ = v_ctors_2063_;
v___y_1992_ = v_asyncMode_2039_;
v___y_1993_ = v___x_2041_;
v___y_1994_ = v_a_2056_;
v___y_1995_ = v___x_2038_;
v___y_1996_ = v_a_2054_;
v___y_1997_ = v_a_1781_;
v___y_1998_ = v_a_1782_;
v___y_1999_ = v_a_1783_;
v___y_2000_ = v_a_1784_;
goto v___jp_1987_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec_ref(v___f_2064_);
lean_dec(v_ctors_2063_);
lean_dec(v_numIndices_2062_);
lean_dec(v_numParams_2061_);
lean_dec(v_a_2056_);
lean_dec(v_a_2054_);
lean_dec_ref(v_ctors_1780_);
lean_dec(v_indName_1779_);
v___x_2068_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__9, &l_Lean_Meta_mkSparseCasesOn___closed__9_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__9);
v___x_2069_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_2068_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_a_2056_);
lean_dec(v_a_2054_);
lean_dec_ref_known(v___x_2040_, 2);
lean_dec_ref(v_ctors_1780_);
lean_dec(v_indName_1779_);
v_a_2078_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2060_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2060_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v_a_2054_);
lean_dec_ref_known(v___x_2040_, 2);
lean_dec_ref(v_ctors_1780_);
lean_dec(v_indName_1779_);
v_a_2086_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2055_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2055_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object* v_indName_2096_, lean_object* v_ctors_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Meta_mkSparseCasesOn(v_indName_2096_, v_ctors_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object* v_00_u03b2_2104_, lean_object* v_x_2105_, lean_object* v_x_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_2105_, v_x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object* v_00_u03b2_2108_, lean_object* v_x_2109_, lean_object* v_x_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(v_00_u03b2_2108_, v_x_2109_, v_x_2110_);
lean_dec_ref(v_x_2110_);
lean_dec_ref(v_x_2109_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object* v_00_u03b2_2112_, lean_object* v_x_2113_, lean_object* v_x_2114_, lean_object* v_x_2115_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_x_2113_, v_x_2114_, v_x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(lean_object* v_00_u03b1_2117_, lean_object* v_name_2118_, uint8_t v_bi_2119_, lean_object* v_type_2120_, lean_object* v_k_2121_, uint8_t v_kind_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_2118_, v_bi_2119_, v_type_2120_, v_k_2121_, v_kind_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___boxed(lean_object* v_00_u03b1_2129_, lean_object* v_name_2130_, lean_object* v_bi_2131_, lean_object* v_type_2132_, lean_object* v_k_2133_, lean_object* v_kind_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
uint8_t v_bi_boxed_2140_; uint8_t v_kind_boxed_2141_; lean_object* v_res_2142_; 
v_bi_boxed_2140_ = lean_unbox(v_bi_2131_);
v_kind_boxed_2141_ = lean_unbox(v_kind_2134_);
v_res_2142_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(v_00_u03b1_2129_, v_name_2130_, v_bi_boxed_2140_, v_type_2132_, v_k_2133_, v_kind_boxed_2141_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(lean_object* v_00_u03b1_2143_, lean_object* v_name_2144_, lean_object* v_type_2145_, lean_object* v_k_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v_name_2144_, v_type_2145_, v_k_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object* v_00_u03b1_2153_, lean_object* v_name_2154_, lean_object* v_type_2155_, lean_object* v_k_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_00_u03b1_2153_, v_name_2154_, v_type_2155_, v_k_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object* v_00_u03b1_2163_, lean_object* v_msg_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object* v_00_u03b1_2171_, lean_object* v_msg_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_00_u03b1_2171_, v_msg_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(lean_object* v_declName_2179_, uint8_t v_s_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_2179_, v_s_2180_, v___y_2182_, v___y_2184_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___boxed(lean_object* v_declName_2187_, lean_object* v_s_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
uint8_t v_s_boxed_2194_; lean_object* v_res_2195_; 
v_s_boxed_2194_ = lean_unbox(v_s_2188_);
v_res_2195_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(v_declName_2187_, v_s_boxed_2194_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object* v_00_u03b2_2196_, lean_object* v_x_2197_, size_t v_x_2198_, lean_object* v_x_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_2197_, v_x_2198_, v_x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
size_t v_x_23803__boxed_2205_; lean_object* v_res_2206_; 
v_x_23803__boxed_2205_ = lean_unbox_usize(v_x_2203_);
lean_dec(v_x_2203_);
v_res_2206_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(v_00_u03b2_2201_, v_x_2202_, v_x_23803__boxed_2205_, v_x_2204_);
lean_dec_ref(v_x_2204_);
lean_dec_ref(v_x_2202_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object* v_00_u03b2_2207_, lean_object* v_x_2208_, size_t v_x_2209_, size_t v_x_2210_, lean_object* v_x_2211_, lean_object* v_x_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_2208_, v_x_2209_, v_x_2210_, v_x_2211_, v_x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2214_, lean_object* v_x_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
size_t v_x_23814__boxed_2220_; size_t v_x_23815__boxed_2221_; lean_object* v_res_2222_; 
v_x_23814__boxed_2220_ = lean_unbox_usize(v_x_2216_);
lean_dec(v_x_2216_);
v_x_23815__boxed_2221_ = lean_unbox_usize(v_x_2217_);
lean_dec(v_x_2217_);
v_res_2222_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(v_00_u03b2_2214_, v_x_2215_, v_x_23814__boxed_2220_, v_x_23815__boxed_2221_, v_x_2218_, v_x_2219_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(lean_object* v_00_u03b1_2223_, lean_object* v_constName_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_constName_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(v_00_u03b1_2231_, v_constName_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2239_, lean_object* v_keys_2240_, lean_object* v_vals_2241_, lean_object* v_heq_2242_, lean_object* v_i_2243_, lean_object* v_k_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_keys_2240_, v_vals_2241_, v_i_2243_, v_k_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___boxed(lean_object* v_00_u03b2_2246_, lean_object* v_keys_2247_, lean_object* v_vals_2248_, lean_object* v_heq_2249_, lean_object* v_i_2250_, lean_object* v_k_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(v_00_u03b2_2246_, v_keys_2247_, v_vals_2248_, v_heq_2249_, v_i_2250_, v_k_2251_);
lean_dec_ref(v_k_2251_);
lean_dec_ref(v_vals_2248_);
lean_dec_ref(v_keys_2247_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2253_, lean_object* v_n_2254_, lean_object* v_k_2255_, lean_object* v_v_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(v_n_2254_, v_k_2255_, v_v_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2258_, size_t v_depth_2259_, lean_object* v_keys_2260_, lean_object* v_vals_2261_, lean_object* v_heq_2262_, lean_object* v_i_2263_, lean_object* v_entries_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_depth_2259_, v_keys_2260_, v_vals_2261_, v_i_2263_, v_entries_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___boxed(lean_object* v_00_u03b2_2266_, lean_object* v_depth_2267_, lean_object* v_keys_2268_, lean_object* v_vals_2269_, lean_object* v_heq_2270_, lean_object* v_i_2271_, lean_object* v_entries_2272_){
_start:
{
size_t v_depth_boxed_2273_; lean_object* v_res_2274_; 
v_depth_boxed_2273_ = lean_unbox_usize(v_depth_2267_);
lean_dec(v_depth_2267_);
v_res_2274_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(v_00_u03b2_2266_, v_depth_boxed_2273_, v_keys_2268_, v_vals_2269_, v_heq_2270_, v_i_2271_, v_entries_2272_);
lean_dec_ref(v_vals_2269_);
lean_dec_ref(v_keys_2268_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(lean_object* v_00_u03b1_2275_, lean_object* v_ref_2276_, lean_object* v_constName_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_2276_, v_constName_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___boxed(lean_object* v_00_u03b1_2284_, lean_object* v_ref_2285_, lean_object* v_constName_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(v_00_u03b1_2284_, v_ref_2285_, v_constName_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v_ref_2285_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26(lean_object* v_00_u03b2_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(v_x_2294_, v_x_2295_, v_x_2296_, v_x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(lean_object* v_00_u03b1_2299_, lean_object* v_ref_2300_, lean_object* v_msg_2301_, lean_object* v_declHint_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_2300_, v_msg_2301_, v_declHint_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___boxed(lean_object* v_00_u03b1_2309_, lean_object* v_ref_2310_, lean_object* v_msg_2311_, lean_object* v_declHint_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(v_00_u03b1_2309_, v_ref_2310_, v_msg_2311_, v_declHint_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v_ref_2310_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(lean_object* v_msg_2319_, lean_object* v_declHint_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_2319_, v_declHint_2320_, v___y_2324_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___boxed(lean_object* v_msg_2327_, lean_object* v_declHint_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(v_msg_2327_, v_declHint_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(lean_object* v_00_u03b1_2335_, lean_object* v_ref_2336_, lean_object* v_msg_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_2336_, v_msg_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___boxed(lean_object* v_00_u03b1_2344_, lean_object* v_ref_2345_, lean_object* v_msg_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(v_00_u03b1_2344_, v_ref_2345_, v_msg_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v_ref_2345_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object* v_env_2353_, lean_object* v_sparseCasesOnName_2354_){
_start:
{
lean_object* v___x_2355_; lean_object* v_toEnvExtension_2356_; lean_object* v_asyncMode_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; 
v___x_2355_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2356_ = lean_ctor_get(v___x_2355_, 0);
v_asyncMode_2357_ = lean_ctor_get(v_toEnvExtension_2356_, 2);
v___x_2358_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2359_ = 0;
v___x_2360_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2358_, v___x_2355_, v_env_2353_, v_sparseCasesOnName_2354_, v_asyncMode_2357_, v___x_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object* v_sparseCasesOnName_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v_env_2365_; lean_object* v___x_2366_; lean_object* v_toEnvExtension_2367_; lean_object* v_asyncMode_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2364_ = lean_st_ref_get(v_a_2362_);
v_env_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc_ref(v_env_2365_);
lean_dec(v___x_2364_);
v___x_2366_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2367_ = lean_ctor_get(v___x_2366_, 0);
v_asyncMode_2368_ = lean_ctor_get(v_toEnvExtension_2367_, 2);
v___x_2369_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2370_ = 0;
v___x_2371_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2369_, v___x_2366_, v_env_2365_, v_sparseCasesOnName_2361_, v_asyncMode_2368_, v___x_2370_);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object* v_sparseCasesOnName_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2373_, v_a_2374_);
lean_dec(v_a_2374_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object* v_sparseCasesOnName_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2377_, v_a_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object* v_sparseCasesOnName_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Meta_getSparseCasesOnInfo(v_sparseCasesOnName_2382_, v_a_2383_, v_a_2384_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
return v_res_2386_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
}
#ifdef __cplusplus
}
#endif
