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
lean_object* v___f_392_; lean_object* v___x_16834__overap_393_; lean_object* v___x_394_; 
v___f_392_ = ((lean_object*)(l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0));
v___x_16834__overap_393_ = lean_panic_fn_borrowed(v___f_392_, v_msg_386_);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
v___x_394_ = lean_apply_5(v___x_16834__overap_393_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, lean_box(0));
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
size_t v_x_20858__boxed_541_; size_t v_x_20859__boxed_542_; lean_object* v_res_543_; 
v_x_20858__boxed_541_ = lean_unbox_usize(v_x_537_);
lean_dec(v_x_537_);
v_x_20859__boxed_542_ = lean_unbox_usize(v_x_538_);
lean_dec(v_x_538_);
v_res_543_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_536_, v_x_20858__boxed_541_, v_x_20859__boxed_542_, v_x_539_, v_x_540_);
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
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_17113__overap_642_; lean_object* v___x_643_; 
v___x_640_ = lean_box(0);
v___x_641_ = l_instInhabitedOfMonad___redArg(v___x_639_, v___x_640_);
v___x_17113__overap_642_ = lean_panic_fn_borrowed(v___x_641_, v_msg_585_);
lean_dec(v___x_641_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
v___x_643_ = lean_apply_5(v___x_17113__overap_642_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, lean_box(0));
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
lean_object* v___x_669_; lean_object* v_env_670_; lean_object* v___x_671_; lean_object* v_toCold_672_; lean_object* v_mctx_673_; lean_object* v_lctx_674_; lean_object* v_options_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_669_ = lean_st_ref_get(v___y_667_);
v_env_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc_ref(v_env_670_);
lean_dec(v___x_669_);
v___x_671_ = lean_st_ref_get(v___y_665_);
v_toCold_672_ = lean_ctor_get(v___y_666_, 0);
v_mctx_673_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref(v_mctx_673_);
lean_dec(v___x_671_);
v_lctx_674_ = lean_ctor_get(v___y_664_, 2);
v_options_675_ = lean_ctor_get(v_toCold_672_, 2);
lean_inc_ref(v_options_675_);
lean_inc_ref(v_lctx_674_);
v___x_676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_676_, 0, v_env_670_);
lean_ctor_set(v___x_676_, 1, v_mctx_673_);
lean_ctor_set(v___x_676_, 2, v_lctx_674_);
lean_ctor_set(v___x_676_, 3, v_options_675_);
v___x_677_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v_msgData_663_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19___boxed(lean_object* v_msgData_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(v_msgData_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(lean_object* v_msg_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_ref_692_; lean_object* v___x_693_; lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_702_; 
v_ref_692_ = lean_ctor_get(v___y_689_, 2);
v___x_693_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(v_msg_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_702_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
lean_inc(v_ref_692_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_ref_692_);
lean_ctor_set(v___x_698_, 1, v_a_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 1);
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg___boxed(lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0));
v___x_712_ = l_Lean_stringToMessageData(v___x_711_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2));
v___x_715_ = l_Lean_stringToMessageData(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_719_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6));
v___x_720_ = lean_unsigned_to_nat(11u);
v___x_721_ = lean_unsigned_to_nat(122u);
v___x_722_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5));
v___x_723_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4));
v___x_724_ = l_mkPanicMessageWithDecl(v___x_723_, v___x_722_, v___x_721_, v___x_720_, v___x_719_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object* v_constName_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_739_; lean_object* v_env_740_; uint8_t v___x_741_; lean_object* v___x_742_; 
v___x_739_ = lean_st_ref_get(v___y_729_);
v_env_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc_ref(v_env_740_);
lean_dec(v___x_739_);
v___x_741_ = 0;
lean_inc(v_constName_725_);
v___x_742_ = l_Lean_Environment_findAsync_x3f(v_env_740_, v_constName_725_, v___x_741_);
if (lean_obj_tag(v___x_742_) == 1)
{
lean_object* v_val_743_; uint8_t v_kind_744_; 
v_val_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_val_743_);
lean_dec_ref_known(v___x_742_, 1);
v_kind_744_ = lean_ctor_get_uint8(v_val_743_, sizeof(void*)*3);
if (v_kind_744_ == 6)
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_743_);
if (lean_obj_tag(v___x_745_) == 6)
{
lean_object* v_val_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_constName_725_);
v_val_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_val_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 0);
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_val_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec_ref(v___x_745_);
v___x_754_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7);
v___x_755_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v___x_754_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_764_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_764_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
if (lean_obj_tag(v_a_756_) == 0)
{
lean_del_object(v___x_758_);
goto v___jp_731_;
}
else
{
lean_object* v_val_760_; lean_object* v___x_762_; 
lean_dec(v_constName_725_);
v_val_760_ = lean_ctor_get(v_a_756_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v_a_756_, 1);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v_val_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_val_760_);
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
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_constName_725_);
v_a_765_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_755_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_755_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
else
{
lean_dec(v_val_743_);
goto v___jp_731_;
}
}
else
{
lean_dec(v___x_742_);
goto v___jp_731_;
}
v___jp_731_:
{
lean_object* v___x_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_732_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_733_ = 0;
v___x_734_ = l_Lean_MessageData_ofConstName(v_constName_725_, v___x_733_);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_732_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_737_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object* v_constName_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_constName_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object* v___x_780_, size_t v_sz_781_, size_t v_i_782_, lean_object* v_bs_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = lean_usize_dec_lt(v_i_782_, v_sz_781_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_bs_783_);
return v___x_790_;
}
else
{
lean_object* v_v_791_; lean_object* v___x_792_; 
v_v_791_ = lean_array_uget_borrowed(v_bs_783_, v_i_782_);
lean_inc(v_v_791_);
v___x_792_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_791_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v_cidx_794_; lean_object* v_start_795_; lean_object* v_stop_796_; lean_object* v___x_797_; lean_object* v_bs_x27_798_; lean_object* v_a_800_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v_cidx_794_ = lean_ctor_get(v_a_793_, 2);
lean_inc(v_cidx_794_);
lean_dec(v_a_793_);
v_start_795_ = lean_ctor_get(v___x_780_, 1);
v_stop_796_ = lean_ctor_get(v___x_780_, 2);
v___x_797_ = lean_unsigned_to_nat(0u);
v_bs_x27_798_ = lean_array_uset(v_bs_783_, v_i_782_, v___x_797_);
v___x_805_ = lean_nat_sub(v_stop_796_, v_start_795_);
v___x_806_ = lean_nat_dec_lt(v_cidx_794_, v___x_805_);
lean_dec(v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v_cidx_794_);
v___x_807_ = l_Lean_instInhabitedExpr;
v___x_808_ = l_outOfBounds___redArg(v___x_807_);
v_a_800_ = v___x_808_;
goto v___jp_799_;
}
else
{
lean_object* v___x_809_; 
v___x_809_ = l_Subarray_get___redArg(v___x_780_, v_cidx_794_);
lean_dec(v_cidx_794_);
v_a_800_ = v___x_809_;
goto v___jp_799_;
}
v___jp_799_:
{
size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_782_, v___x_801_);
v___x_803_ = lean_array_uset(v_bs_x27_798_, v_i_782_, v_a_800_);
v_i_782_ = v___x_802_;
v_bs_783_ = v___x_803_;
goto _start;
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_bs_783_);
v_a_810_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_792_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_792_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7___boxed(lean_object* v___x_818_, lean_object* v_sz_819_, lean_object* v_i_820_, lean_object* v_bs_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
size_t v_sz_boxed_827_; size_t v_i_boxed_828_; lean_object* v_res_829_; 
v_sz_boxed_827_ = lean_unbox_usize(v_sz_819_);
lean_dec(v_sz_819_);
v_i_boxed_828_ = lean_unbox_usize(v_i_820_);
lean_dec(v_i_820_);
v_res_829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(v___x_818_, v_sz_boxed_827_, v_i_boxed_828_, v_bs_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec_ref(v___x_818_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(lean_object* v_xs_830_, lean_object* v_v_831_, lean_object* v_i_832_){
_start:
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = lean_array_get_size(v_xs_830_);
v___x_834_ = lean_nat_dec_lt(v_i_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_dec(v_i_832_);
v___x_835_ = lean_box(0);
return v___x_835_;
}
else
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_array_fget_borrowed(v_xs_830_, v_i_832_);
v___x_837_ = lean_name_eq(v___x_836_, v_v_831_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_add(v_i_832_, v___x_838_);
lean_dec(v_i_832_);
v_i_832_ = v___x_839_;
goto _start;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v_i_832_);
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23___boxed(lean_object* v_xs_842_, lean_object* v_v_843_, lean_object* v_i_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(v_xs_842_, v_v_843_, v_i_844_);
lean_dec(v_v_843_);
lean_dec_ref(v_xs_842_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(lean_object* v_xs_846_, lean_object* v_v_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(v_xs_846_, v_v_847_, v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15___boxed(lean_object* v_xs_850_, lean_object* v_v_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(v_xs_850_, v_v_851_);
lean_dec(v_v_851_);
lean_dec_ref(v_xs_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object* v_xs_853_, lean_object* v_v_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(v_xs_853_, v_v_854_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v___x_856_; 
v___x_856_ = lean_box(0);
return v___x_856_;
}
else
{
lean_object* v_val_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_val_857_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_855_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_val_857_);
lean_dec(v___x_855_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_val_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object* v_xs_865_, lean_object* v_v_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(v_xs_865_, v_v_866_);
lean_dec(v_v_866_);
lean_dec_ref(v_xs_865_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(lean_object* v_ctors_868_, lean_object* v_a_869_, lean_object* v___x_870_, lean_object* v_a_871_, uint8_t v___x_872_, uint8_t v___x_873_, lean_object* v_a_874_, lean_object* v_ys_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(v_ctors_868_, v_a_869_);
if (lean_obj_tag(v___x_882_) == 1)
{
lean_object* v_val_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; 
lean_dec(v_a_869_);
v_val_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v___x_882_, 1);
lean_inc_ref(v_ys_875_);
v___x_884_ = lean_array_pop(v_ys_875_);
v___x_885_ = lean_array_get_borrowed(v___x_870_, v_a_871_, v_val_883_);
lean_dec(v_val_883_);
lean_inc(v___x_885_);
v___x_886_ = l_Lean_mkAppN(v___x_885_, v___x_884_);
lean_dec_ref(v___x_884_);
v___x_887_ = 1;
v___x_888_ = l_Lean_Meta_mkLambdaFVars(v_ys_875_, v___x_886_, v___x_872_, v___x_873_, v___x_872_, v___x_873_, v___x_887_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec_ref(v_ys_875_);
return v___x_888_;
}
else
{
lean_object* v___x_889_; 
lean_dec(v___x_882_);
v___x_889_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_a_869_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v_cidx_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
v_cidx_891_ = lean_ctor_get(v_a_890_, 2);
lean_inc(v_cidx_891_);
lean_dec(v_a_890_);
v___x_892_ = l_Lean_mkRawNatLit(v_cidx_891_);
v___x_893_ = l_Lean_mkHasNotBitProof(v___x_892_, v_a_874_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; lean_object* v___x_901_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_893_, 1);
v___x_895_ = lean_array_get_size(v_ys_875_);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_nat_sub(v___x_895_, v___x_896_);
v___x_898_ = lean_array_get_borrowed(v___x_870_, v_ys_875_, v___x_897_);
lean_dec(v___x_897_);
lean_inc(v___x_898_);
v___x_899_ = l_Lean_Expr_app___override(v___x_898_, v_a_894_);
v___x_900_ = 1;
v___x_901_ = l_Lean_Meta_mkLambdaFVars(v_ys_875_, v___x_899_, v___x_872_, v___x_873_, v___x_872_, v___x_873_, v___x_900_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec_ref(v_ys_875_);
return v___x_901_;
}
else
{
lean_dec_ref(v_ys_875_);
return v___x_893_;
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v_ys_875_);
v_a_902_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_889_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_889_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0___boxed(lean_object* v_ctors_910_, lean_object* v_a_911_, lean_object* v___x_912_, lean_object* v_a_913_, lean_object* v___x_914_, lean_object* v___x_915_, lean_object* v_a_916_, lean_object* v_ys_917_, lean_object* v_x_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
uint8_t v___x_21516__boxed_924_; uint8_t v___x_21517__boxed_925_; lean_object* v_res_926_; 
v___x_21516__boxed_924_ = lean_unbox(v___x_914_);
v___x_21517__boxed_925_ = lean_unbox(v___x_915_);
v_res_926_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(v_ctors_910_, v_a_911_, v___x_912_, v_a_913_, v___x_21516__boxed_924_, v___x_21517__boxed_925_, v_a_916_, v_ys_917_, v_x_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec_ref(v_x_918_);
lean_dec_ref(v_a_916_);
lean_dec_ref(v_a_913_);
lean_dec_ref(v___x_912_);
lean_dec_ref(v_ctors_910_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object* v_ctors_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_as_930_, lean_object* v_bs_931_, lean_object* v_i_932_, lean_object* v_cs_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_array_get_size(v_as_930_);
v___x_940_ = lean_nat_dec_lt(v_i_932_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
lean_dec(v_i_932_);
lean_dec_ref(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v_ctors_927_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v_cs_933_);
return v___x_941_;
}
else
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_array_get_size(v_bs_931_);
v___x_943_ = lean_nat_dec_lt(v_i_932_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
lean_dec(v_i_932_);
lean_dec_ref(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v_ctors_927_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_cs_933_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v_a_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___f_950_; lean_object* v_b_951_; lean_object* v___x_952_; 
v___x_945_ = l_Lean_instInhabitedExpr;
v___x_946_ = 0;
v_a_947_ = lean_array_fget_borrowed(v_as_930_, v_i_932_);
v___x_948_ = lean_box(v___x_946_);
v___x_949_ = lean_box(v___x_943_);
lean_inc_ref(v_a_929_);
lean_inc_ref(v_a_928_);
lean_inc(v_a_947_);
lean_inc_ref(v_ctors_927_);
v___f_950_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_950_, 0, v_ctors_927_);
lean_closure_set(v___f_950_, 1, v_a_947_);
lean_closure_set(v___f_950_, 2, v___x_945_);
lean_closure_set(v___f_950_, 3, v_a_928_);
lean_closure_set(v___f_950_, 4, v___x_948_);
lean_closure_set(v___f_950_, 5, v___x_949_);
lean_closure_set(v___f_950_, 6, v_a_929_);
v_b_951_ = lean_array_fget_borrowed(v_bs_931_, v_i_932_);
lean_inc(v_b_951_);
v___x_952_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v_b_951_, v___f_950_, v___x_946_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = lean_unsigned_to_nat(1u);
v___x_955_ = lean_nat_add(v_i_932_, v___x_954_);
lean_dec(v_i_932_);
v___x_956_ = lean_array_push(v_cs_933_, v_a_953_);
v_i_932_ = v___x_955_;
v_cs_933_ = v___x_956_;
goto _start;
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v_cs_933_);
lean_dec(v_i_932_);
lean_dec_ref(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v_ctors_927_);
v_a_958_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_952_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_952_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object* v_ctors_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_as_969_, lean_object* v_bs_970_, lean_object* v_i_971_, lean_object* v_cs_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(v_ctors_966_, v_a_967_, v_a_968_, v_as_969_, v_bs_970_, v_i_971_, v_cs_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec_ref(v_bs_970_);
lean_dec_ref(v_as_969_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(size_t v_sz_979_, size_t v_i_980_, lean_object* v_bs_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_usize_dec_lt(v_i_980_, v_sz_979_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_bs_981_);
return v___x_988_;
}
else
{
lean_object* v_v_989_; lean_object* v___x_990_; 
v_v_989_ = lean_array_uget_borrowed(v_bs_981_, v_i_980_);
lean_inc(v_v_989_);
v___x_990_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_989_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v_cidx_992_; lean_object* v___x_993_; lean_object* v_bs_x27_994_; size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v_cidx_992_ = lean_ctor_get(v_a_991_, 2);
lean_inc(v_cidx_992_);
lean_dec(v_a_991_);
v___x_993_ = lean_unsigned_to_nat(0u);
v_bs_x27_994_ = lean_array_uset(v_bs_981_, v_i_980_, v___x_993_);
v___x_995_ = ((size_t)1ULL);
v___x_996_ = lean_usize_add(v_i_980_, v___x_995_);
v___x_997_ = lean_array_uset(v_bs_x27_994_, v_i_980_, v_cidx_992_);
v_i_980_ = v___x_996_;
v_bs_981_ = v___x_997_;
goto _start;
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v_bs_981_);
v_a_999_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_990_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_990_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object* v_sz_1007_, lean_object* v_i_1008_, lean_object* v_bs_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
size_t v_sz_boxed_1015_; size_t v_i_boxed_1016_; lean_object* v_res_1017_; 
v_sz_boxed_1015_ = lean_unbox_usize(v_sz_1007_);
lean_dec(v_sz_1007_);
v_i_boxed_1016_ = lean_unbox_usize(v_i_1008_);
lean_dec(v_i_1008_);
v_res_1017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v_sz_boxed_1015_, v_i_boxed_1016_, v_bs_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0(lean_object* v_k_1018_, lean_object* v_b_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
lean_inc(v___y_1023_);
lean_inc_ref(v___y_1022_);
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
v___x_1025_ = lean_apply_6(v_k_1018_, v_b_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, lean_box(0));
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0___boxed(lean_object* v_k_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0(v_k_1026_, v_b_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(lean_object* v_name_1034_, uint8_t v_bi_1035_, lean_object* v_type_1036_, lean_object* v_k_1037_, uint8_t v_kind_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___f_1044_; lean_object* v___x_1045_; 
v___f_1044_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1044_, 0, v_k_1037_);
v___x_1045_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1034_, v_bi_1035_, v_type_1036_, v___f_1044_, v_kind_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_a_1054_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1045_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1045_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___boxed(lean_object* v_name_1062_, lean_object* v_bi_1063_, lean_object* v_type_1064_, lean_object* v_k_1065_, lean_object* v_kind_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v_bi_boxed_1072_; uint8_t v_kind_boxed_1073_; lean_object* v_res_1074_; 
v_bi_boxed_1072_ = lean_unbox(v_bi_1063_);
v_kind_boxed_1073_ = lean_unbox(v_kind_1066_);
v_res_1074_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_1062_, v_bi_boxed_1072_, v_type_1064_, v_k_1065_, v_kind_boxed_1073_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(lean_object* v_name_1075_, lean_object* v_type_1076_, lean_object* v_k_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
uint8_t v___x_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = 0;
v___x_1084_ = 0;
v___x_1085_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_1075_, v___x_1083_, v_type_1076_, v_k_1077_, v___x_1084_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg___boxed(lean_object* v_name_1086_, lean_object* v_type_1087_, lean_object* v_k_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v_name_1086_, v_type_1087_, v_k_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1094_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object* v_numParams_1106_, lean_object* v___x_1107_, lean_object* v_numIndices_1108_, lean_object* v_ctors_1109_, lean_object* v___x_1110_, lean_object* v___x_1111_, lean_object* v_a_1112_, lean_object* v_ctors_1113_, lean_object* v___x_1114_, lean_object* v_xs_1115_, lean_object* v_x_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1230_ = lean_array_get_size(v_xs_1115_);
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_add(v_numParams_1106_, v___x_1231_);
v___x_1233_ = lean_nat_add(v___x_1232_, v_numIndices_1108_);
lean_dec(v___x_1232_);
v___x_1234_ = lean_nat_add(v___x_1233_, v___x_1231_);
lean_dec(v___x_1233_);
v___x_1235_ = l_List_lengthTR___redArg(v_ctors_1113_);
v___x_1236_ = lean_nat_add(v___x_1234_, v___x_1235_);
lean_dec(v___x_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_nat_dec_eq(v___x_1230_, v___x_1236_);
lean_dec(v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_xs_1115_);
lean_dec(v_ctors_1113_);
lean_dec(v___x_1111_);
lean_dec(v___x_1110_);
lean_dec_ref(v_ctors_1109_);
lean_dec(v_numParams_1106_);
v___x_1238_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6, &l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once, _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6);
v___x_1239_ = l_Lean_MessageData_ofConstName(v___x_1114_, v___x_1237_);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_1242_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
lean_dec(v___x_1114_);
v___y_1123_ = v___y_1117_;
v___y_1124_ = v___y_1118_;
v___y_1125_ = v___y_1119_;
v___y_1126_ = v___y_1120_;
goto v___jp_1122_;
}
v___jp_1122_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; size_t v_sz_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
v___x_1127_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1106_);
lean_inc_ref_n(v_xs_1115_, 2);
v___x_1128_ = l_Array_toSubarray___redArg(v_xs_1115_, v___x_1127_, v_numParams_1106_);
v___x_1129_ = lean_array_get(v___x_1107_, v_xs_1115_, v_numParams_1106_);
v___x_1130_ = lean_unsigned_to_nat(1u);
v___x_1131_ = lean_nat_add(v_numParams_1106_, v___x_1130_);
lean_dec(v_numParams_1106_);
v___x_1132_ = lean_nat_add(v___x_1131_, v_numIndices_1108_);
lean_inc(v___x_1132_);
v___x_1133_ = l_Array_toSubarray___redArg(v_xs_1115_, v___x_1131_, v___x_1132_);
v___x_1134_ = lean_array_get(v___x_1107_, v_xs_1115_, v___x_1132_);
v___x_1135_ = lean_nat_add(v___x_1132_, v___x_1130_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_array_get_size(v_xs_1115_);
v___x_1137_ = l_Array_toSubarray___redArg(v_xs_1115_, v___x_1135_, v___x_1136_);
v_sz_1138_ = lean_array_size(v_ctors_1109_);
v___x_1139_ = ((size_t)0ULL);
lean_inc_ref(v_ctors_1109_);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(v___x_1137_, v_sz_1138_, v___x_1139_, v_ctors_1109_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec_ref(v___x_1137_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
lean_inc_ref(v_ctors_1109_);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v_sz_1138_, v___x_1139_, v_ctors_1109_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = l_Subarray_copy___redArg(v___x_1133_);
v___x_1145_ = lean_mk_empty_array_with_capacity(v___x_1130_);
lean_inc(v___x_1134_);
lean_inc_ref_n(v___x_1145_, 2);
v___x_1146_ = lean_array_push(v___x_1145_, v___x_1134_);
lean_inc_ref(v___x_1144_);
v___x_1147_ = l_Array_append___redArg(v___x_1144_, v___x_1146_);
lean_inc_ref(v___x_1147_);
lean_inc(v___x_1129_);
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1148_, 0, v___x_1145_);
lean_closure_set(v___f_1148_, 1, v___x_1129_);
lean_closure_set(v___f_1148_, 2, v___x_1147_);
v___x_1149_ = l_Lean_mkConst(v___x_1110_, v___x_1111_);
v___x_1150_ = l_Subarray_copy___redArg(v___x_1128_);
lean_inc_ref(v___x_1150_);
v___x_1151_ = l_Array_append___redArg(v___x_1150_, v___x_1144_);
v___x_1152_ = l_Array_append___redArg(v___x_1151_, v___x_1146_);
v___x_1153_ = l_Lean_mkAppN(v___x_1149_, v___x_1152_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = l_Lean_mkHasNotBit(v___x_1153_, v_a_1143_);
v___x_1155_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1));
v___x_1156_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v___x_1155_, v___x_1154_, v___f_1148_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3));
v___x_1159_ = l_Lean_Core_mkFreshUserName(v___x_1158_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; uint8_t v___x_1167_; lean_object* v___x_1168_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
v___x_1161_ = 0;
v___x_1162_ = l_Lean_ConstantInfo_value_x21(v_a_1112_, v___x_1161_);
v___x_1163_ = 0;
lean_inc(v___x_1129_);
v___x_1164_ = l_Lean_mkAppN(v___x_1129_, v___x_1147_);
v___x_1165_ = l_Lean_mkForall(v_a_1160_, v___x_1163_, v_a_1157_, v___x_1164_);
v___x_1166_ = 1;
v___x_1167_ = 1;
v___x_1168_ = l_Lean_Meta_mkLambdaFVars(v___x_1147_, v___x_1165_, v___x_1161_, v___x_1166_, v___x_1161_, v___x_1166_, v___x_1167_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec_ref(v___x_1147_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v___x_1170_ = l_Lean_mkAppN(v___x_1162_, v___x_1150_);
v___x_1171_ = l_Lean_Expr_app___override(v___x_1170_, v_a_1169_);
v___x_1172_ = l_Lean_mkAppN(v___x_1171_, v___x_1144_);
v___x_1173_ = l_Lean_Expr_app___override(v___x_1172_, v___x_1134_);
v___x_1174_ = l_List_lengthTR___redArg(v_ctors_1113_);
lean_inc_ref(v___x_1173_);
v___x_1175_ = l_Lean_Meta_inferArgumentTypesN(v___x_1174_, v___x_1173_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1177_ = lean_array_mk(v_ctors_1113_);
v___x_1178_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4));
lean_inc(v_a_1141_);
v___x_1179_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(v_ctors_1109_, v_a_1141_, v_a_1143_, v___x_1177_, v_a_1176_, v___x_1127_, v___x_1178_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v_a_1176_);
lean_dec_ref(v___x_1177_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_1179_, 1);
v___x_1181_ = l_Lean_mkAppN(v___x_1173_, v_a_1180_);
lean_dec(v_a_1180_);
v___x_1182_ = l_Lean_Core_betaReduce(v___x_1181_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v___x_1184_ = lean_array_push(v___x_1145_, v___x_1129_);
v___x_1185_ = l_Array_append___redArg(v___x_1150_, v___x_1184_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = l_Array_append___redArg(v___x_1185_, v___x_1144_);
lean_dec_ref(v___x_1144_);
v___x_1187_ = l_Array_append___redArg(v___x_1186_, v___x_1146_);
lean_dec_ref(v___x_1146_);
v___x_1188_ = l_Array_append___redArg(v___x_1187_, v_a_1141_);
lean_dec(v_a_1141_);
v___x_1189_ = l_Lean_Meta_mkLambdaFVars(v___x_1188_, v_a_1183_, v___x_1161_, v___x_1166_, v___x_1161_, v___x_1166_, v___x_1167_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec_ref(v___x_1188_);
return v___x_1189_;
}
else
{
lean_dec_ref(v___x_1150_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec(v_a_1141_);
lean_dec(v___x_1129_);
return v___x_1182_;
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref(v___x_1173_);
lean_dec_ref(v___x_1150_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec(v_a_1141_);
lean_dec(v___x_1129_);
v_a_1190_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1179_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1179_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v___x_1173_);
lean_dec_ref(v___x_1150_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec(v_a_1143_);
lean_dec(v_a_1141_);
lean_dec(v___x_1129_);
lean_dec(v_ctors_1113_);
lean_dec_ref(v_ctors_1109_);
v_a_1198_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1175_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1175_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_dec_ref(v___x_1162_);
lean_dec_ref(v___x_1150_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec(v_a_1143_);
lean_dec(v_a_1141_);
lean_dec(v___x_1134_);
lean_dec(v___x_1129_);
lean_dec(v_ctors_1113_);
lean_dec_ref(v_ctors_1109_);
return v___x_1168_;
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_a_1157_);
lean_dec_ref(v___x_1150_);
lean_dec_ref(v___x_1147_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec(v_a_1143_);
lean_dec(v_a_1141_);
lean_dec(v___x_1134_);
lean_dec(v___x_1129_);
lean_dec(v_ctors_1113_);
lean_dec_ref(v_ctors_1109_);
v_a_1206_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1159_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1159_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_dec_ref(v___x_1150_);
lean_dec_ref(v___x_1147_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec(v_a_1143_);
lean_dec(v_a_1141_);
lean_dec(v___x_1134_);
lean_dec(v___x_1129_);
lean_dec(v_ctors_1113_);
lean_dec_ref(v_ctors_1109_);
return v___x_1156_;
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_a_1141_);
lean_dec(v___x_1134_);
lean_dec_ref(v___x_1133_);
lean_dec(v___x_1129_);
lean_dec_ref(v___x_1128_);
lean_dec(v_ctors_1113_);
lean_dec(v___x_1111_);
lean_dec(v___x_1110_);
lean_dec_ref(v_ctors_1109_);
v_a_1214_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1142_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1142_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v___x_1134_);
lean_dec_ref(v___x_1133_);
lean_dec(v___x_1129_);
lean_dec_ref(v___x_1128_);
lean_dec(v_ctors_1113_);
lean_dec(v___x_1111_);
lean_dec(v___x_1110_);
lean_dec_ref(v_ctors_1109_);
v_a_1222_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1140_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1140_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object* v_numParams_1252_, lean_object* v___x_1253_, lean_object* v_numIndices_1254_, lean_object* v_ctors_1255_, lean_object* v___x_1256_, lean_object* v___x_1257_, lean_object* v_a_1258_, lean_object* v_ctors_1259_, lean_object* v___x_1260_, lean_object* v_xs_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Meta_mkSparseCasesOn___lam__2(v_numParams_1252_, v___x_1253_, v_numIndices_1254_, v_ctors_1255_, v___x_1256_, v___x_1257_, v_a_1258_, v_ctors_1259_, v___x_1260_, v_xs_1261_, v_x_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec_ref(v_x_1262_);
lean_dec_ref(v_a_1258_);
lean_dec(v_numIndices_1254_);
lean_dec_ref(v___x_1253_);
return v_res_1268_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object* v_a_1269_, lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1270_) == 0)
{
uint8_t v___x_1271_; 
v___x_1271_ = 0;
return v___x_1271_;
}
else
{
lean_object* v_head_1272_; lean_object* v_tail_1273_; uint8_t v___x_1274_; 
v_head_1272_ = lean_ctor_get(v_x_1270_, 0);
v_tail_1273_ = lean_ctor_get(v_x_1270_, 1);
v___x_1274_ = lean_name_eq(v_a_1269_, v_head_1272_);
if (v___x_1274_ == 0)
{
v_x_1270_ = v_tail_1273_;
goto _start;
}
else
{
return v___x_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object* v_a_1276_, lean_object* v_x_1277_){
_start:
{
uint8_t v_res_1278_; lean_object* v_r_1279_; 
v_res_1278_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_a_1276_, v_x_1277_);
lean_dec(v_x_1277_);
lean_dec(v_a_1276_);
v_r_1279_ = lean_box(v_res_1278_);
return v_r_1279_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0));
v___x_1282_ = l_Lean_stringToMessageData(v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object* v_a_1286_, lean_object* v_indName_1287_, lean_object* v_as_1288_, size_t v_sz_1289_, size_t v_i_1290_, lean_object* v_b_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_a_1298_; uint8_t v___x_1302_; 
v___x_1302_ = lean_usize_dec_lt(v_i_1290_, v_sz_1289_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec(v_indName_1287_);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_b_1291_);
return v___x_1303_;
}
else
{
lean_object* v_ctors_1304_; lean_object* v___x_1305_; lean_object* v_a_1306_; uint8_t v___x_1307_; 
v_ctors_1304_ = lean_ctor_get(v_a_1286_, 4);
v___x_1305_ = lean_box(0);
v_a_1306_ = lean_array_uget_borrowed(v_as_1288_, v_i_1290_);
v___x_1307_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_a_1306_, v_ctors_1304_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1308_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1);
lean_inc(v_a_1306_);
v___x_1309_ = l_Lean_MessageData_ofName(v_a_1306_);
v___x_1310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3);
v___x_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
lean_inc(v_indName_1287_);
v___x_1313_ = l_Lean_MessageData_ofName(v_indName_1287_);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_1314_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_dec_ref_known(v___x_1315_, 1);
v_a_1298_ = v___x_1305_;
goto v___jp_1297_;
}
else
{
lean_dec(v_indName_1287_);
return v___x_1315_;
}
}
else
{
v_a_1298_ = v___x_1305_;
goto v___jp_1297_;
}
}
v___jp_1297_:
{
size_t v___x_1299_; size_t v___x_1300_; 
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1290_, v___x_1299_);
v_i_1290_ = v___x_1300_;
v_b_1291_ = v_a_1298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object* v_a_1316_, lean_object* v_indName_1317_, lean_object* v_as_1318_, lean_object* v_sz_1319_, lean_object* v_i_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
size_t v_sz_boxed_1327_; size_t v_i_boxed_1328_; lean_object* v_res_1329_; 
v_sz_boxed_1327_ = lean_unbox_usize(v_sz_1319_);
lean_dec(v_sz_1319_);
v_i_boxed_1328_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v_res_1329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_1316_, v_indName_1317_, v_as_1318_, v_sz_boxed_1327_, v_i_boxed_1328_, v_b_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v_as_1318_);
lean_dec_ref(v_a_1316_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
if (lean_obj_tag(v_a_1330_) == 0)
{
lean_object* v___x_1332_; 
v___x_1332_ = l_List_reverse___redArg(v_a_1331_);
return v___x_1332_;
}
else
{
lean_object* v_head_1333_; lean_object* v_tail_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1343_; 
v_head_1333_ = lean_ctor_get(v_a_1330_, 0);
v_tail_1334_ = lean_ctor_get(v_a_1330_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_a_1330_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1336_ = v_a_1330_;
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_tail_1334_);
lean_inc(v_head_1333_);
lean_dec(v_a_1330_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = l_Lean_mkLevelParam(v_head_1333_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v_a_1331_);
lean_ctor_set(v___x_1336_, 0, v___x_1338_);
v___x_1340_ = v___x_1336_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_a_1331_);
v___x_1340_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
v_a_1330_ = v_tail_1334_;
v_a_1331_ = v___x_1340_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
return v___x_1348_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1);
v___x_1350_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
lean_ctor_set(v___x_1350_, 2, v___x_1349_);
lean_ctor_set(v___x_1350_, 3, v___x_1349_);
lean_ctor_set(v___x_1350_, 4, v___x_1349_);
lean_ctor_set(v___x_1350_, 5, v___x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(lean_object* v_declName_1351_, uint8_t v_s_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v_env_1357_; lean_object* v_nextMacroScope_1358_; lean_object* v_ngen_1359_; lean_object* v_auxDeclNGen_1360_; lean_object* v_traceState_1361_; lean_object* v_messages_1362_; lean_object* v_infoState_1363_; lean_object* v_snapshotTasks_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1393_; 
v___x_1356_ = lean_st_ref_take(v___y_1354_);
v_env_1357_ = lean_ctor_get(v___x_1356_, 0);
v_nextMacroScope_1358_ = lean_ctor_get(v___x_1356_, 1);
v_ngen_1359_ = lean_ctor_get(v___x_1356_, 2);
v_auxDeclNGen_1360_ = lean_ctor_get(v___x_1356_, 3);
v_traceState_1361_ = lean_ctor_get(v___x_1356_, 4);
v_messages_1362_ = lean_ctor_get(v___x_1356_, 6);
v_infoState_1363_ = lean_ctor_get(v___x_1356_, 7);
v_snapshotTasks_1364_ = lean_ctor_get(v___x_1356_, 8);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v___x_1356_, 5);
lean_dec(v_unused_1394_);
v___x_1366_ = v___x_1356_;
v_isShared_1367_ = v_isSharedCheck_1393_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_snapshotTasks_1364_);
lean_inc(v_infoState_1363_);
lean_inc(v_messages_1362_);
lean_inc(v_traceState_1361_);
lean_inc(v_auxDeclNGen_1360_);
lean_inc(v_ngen_1359_);
lean_inc(v_nextMacroScope_1358_);
lean_inc(v_env_1357_);
lean_dec(v___x_1356_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1393_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
uint8_t v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1368_ = 0;
v___x_1369_ = lean_box(0);
v___x_1370_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1357_, v_declName_1351_, v_s_1352_, v___x_1368_, v___x_1369_);
v___x_1371_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 5, v___x_1371_);
lean_ctor_set(v___x_1366_, 0, v___x_1370_);
v___x_1373_ = v___x_1366_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_nextMacroScope_1358_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_ngen_1359_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_auxDeclNGen_1360_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v_traceState_1361_);
lean_ctor_set(v_reuseFailAlloc_1392_, 5, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1392_, 6, v_messages_1362_);
lean_ctor_set(v_reuseFailAlloc_1392_, 7, v_infoState_1363_);
lean_ctor_set(v_reuseFailAlloc_1392_, 8, v_snapshotTasks_1364_);
v___x_1373_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_mctx_1376_; lean_object* v_zetaDeltaFVarIds_1377_; lean_object* v_postponed_1378_; lean_object* v_diag_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1390_; 
v___x_1374_ = lean_st_ref_put(v___y_1354_, v___x_1373_);
v___x_1375_ = lean_st_ref_take(v___y_1353_);
v_mctx_1376_ = lean_ctor_get(v___x_1375_, 0);
v_zetaDeltaFVarIds_1377_ = lean_ctor_get(v___x_1375_, 2);
v_postponed_1378_ = lean_ctor_get(v___x_1375_, 3);
v_diag_1379_ = lean_ctor_get(v___x_1375_, 4);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; 
v_unused_1391_ = lean_ctor_get(v___x_1375_, 1);
lean_dec(v_unused_1391_);
v___x_1381_ = v___x_1375_;
v_isShared_1382_ = v_isSharedCheck_1390_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_diag_1379_);
lean_inc(v_postponed_1378_);
lean_inc(v_zetaDeltaFVarIds_1377_);
lean_inc(v_mctx_1376_);
lean_dec(v___x_1375_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1390_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v___x_1383_);
v___x_1385_ = v___x_1381_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_mctx_1376_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_zetaDeltaFVarIds_1377_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_postponed_1378_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v_diag_1379_);
v___x_1385_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = lean_st_ref_put(v___y_1353_, v___x_1385_);
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___boxed(lean_object* v_declName_1395_, lean_object* v_s_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v_s_boxed_1400_; lean_object* v_res_1401_; 
v_s_boxed_1400_ = lean_unbox(v_s_1396_);
v_res_1401_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_1395_, v_s_boxed_1400_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec(v___y_1397_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object* v_declName_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = 0;
v___x_1409_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_1402_, v___x_1408_, v___y_1404_, v___y_1406_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object* v_declName_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(v_declName_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1416_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0));
v___x_1419_ = l_Lean_stringToMessageData(v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object* v_constName_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; lean_object* v_env_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_st_ref_get(v___y_1424_);
v_env_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc_ref(v_env_1427_);
lean_dec(v___x_1426_);
lean_inc(v_constName_1420_);
v___x_1428_ = l_Lean_isInductiveCore_x3f(v_env_1427_, v_constName_1420_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v___x_1429_; uint8_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1429_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_1430_ = 0;
v___x_1431_ = l_Lean_MessageData_ofConstName(v_constName_1420_, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1429_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_1434_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
return v___x_1435_;
}
else
{
lean_object* v_val_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_constName_1420_);
v_val_1436_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1428_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_val_1436_);
lean_dec(v___x_1428_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set_tag(v___x_1438_, 0);
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_val_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object* v_constName_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(v_constName_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(lean_object* v_ref_1451_, lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_toCold_1458_; lean_object* v_currRecDepth_1459_; lean_object* v_ref_1460_; uint8_t v_diag_1461_; uint8_t v_suppressElabErrors_1462_; lean_object* v_ref_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_toCold_1458_ = lean_ctor_get(v___y_1455_, 0);
v_currRecDepth_1459_ = lean_ctor_get(v___y_1455_, 1);
v_ref_1460_ = lean_ctor_get(v___y_1455_, 2);
v_diag_1461_ = lean_ctor_get_uint8(v___y_1455_, sizeof(void*)*3);
v_suppressElabErrors_1462_ = lean_ctor_get_uint8(v___y_1455_, sizeof(void*)*3 + 1);
v_ref_1463_ = l_Lean_replaceRef(v_ref_1451_, v_ref_1460_);
lean_inc(v_currRecDepth_1459_);
lean_inc_ref(v_toCold_1458_);
v___x_1464_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1464_, 0, v_toCold_1458_);
lean_ctor_set(v___x_1464_, 1, v_currRecDepth_1459_);
lean_ctor_set(v___x_1464_, 2, v_ref_1463_);
lean_ctor_set_uint8(v___x_1464_, sizeof(void*)*3, v_diag_1461_);
lean_ctor_set_uint8(v___x_1464_, sizeof(void*)*3 + 1, v_suppressElabErrors_1462_);
v___x_1465_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_1452_, v___y_1453_, v___y_1454_, v___x_1464_, v___y_1456_);
lean_dec_ref_known(v___x_1464_, 3);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg___boxed(lean_object* v_ref_1466_, lean_object* v_msg_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_1466_, v_msg_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v_ref_1466_);
return v_res_1473_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0(void){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
lean_ctor_set(v___x_1479_, 2, v___x_1478_);
lean_ctor_set(v___x_1479_, 3, v___x_1478_);
lean_ctor_set(v___x_1479_, 4, v___x_1477_);
lean_ctor_set(v___x_1479_, 5, v___x_1477_);
lean_ctor_set(v___x_1479_, 6, v___x_1477_);
lean_ctor_set(v___x_1479_, 7, v___x_1477_);
lean_ctor_set(v___x_1479_, 8, v___x_1477_);
lean_ctor_set(v___x_1479_, 9, v___x_1477_);
lean_ctor_set(v___x_1479_, 10, v___x_1477_);
return v___x_1479_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = lean_unsigned_to_nat(32u);
v___x_1481_ = lean_mk_empty_array_with_capacity(v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4(void){
_start:
{
size_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = ((size_t)5ULL);
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_unsigned_to_nat(32u);
v___x_1486_ = lean_mk_empty_array_with_capacity(v___x_1485_);
v___x_1487_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3);
v___x_1488_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v___x_1486_);
lean_ctor_set(v___x_1488_, 2, v___x_1484_);
lean_ctor_set(v___x_1488_, 3, v___x_1484_);
lean_ctor_set_usize(v___x_1488_, 4, v___x_1483_);
return v___x_1488_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1489_ = lean_box(1);
v___x_1490_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4);
v___x_1491_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1);
v___x_1492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
lean_ctor_set(v___x_1492_, 2, v___x_1489_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8));
v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10));
v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16));
v___x_1510_ = l_Lean_stringToMessageData(v___x_1509_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18));
v___x_1513_ = l_Lean_stringToMessageData(v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(lean_object* v_msg_1514_, lean_object* v_declHint_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v_env_1519_; uint8_t v___x_1520_; 
v___x_1518_ = lean_st_ref_get(v___y_1516_);
v_env_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc_ref(v_env_1519_);
lean_dec(v___x_1518_);
v___x_1520_ = l_Lean_Name_isAnonymous(v_declHint_1515_);
if (v___x_1520_ == 0)
{
uint8_t v_isExporting_1521_; 
v_isExporting_1521_ = lean_ctor_get_uint8(v_env_1519_, sizeof(void*)*8);
if (v_isExporting_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_dec_ref(v_env_1519_);
lean_dec(v_declHint_1515_);
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_msg_1514_);
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
lean_inc_ref(v_env_1519_);
v___x_1523_ = l_Lean_Environment_setExporting(v_env_1519_, v___x_1520_);
lean_inc(v_declHint_1515_);
lean_inc_ref(v___x_1523_);
v___x_1524_ = l_Lean_Environment_contains(v___x_1523_, v_declHint_1515_, v_isExporting_1521_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
lean_dec_ref(v___x_1523_);
lean_dec_ref(v_env_1519_);
lean_dec(v_declHint_1515_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_msg_1514_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v_c_1531_; lean_object* v___x_1532_; 
v___x_1526_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2);
v___x_1527_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5);
v___x_1528_ = l_Lean_Options_empty;
v___x_1529_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1523_);
lean_ctor_set(v___x_1529_, 1, v___x_1526_);
lean_ctor_set(v___x_1529_, 2, v___x_1527_);
lean_ctor_set(v___x_1529_, 3, v___x_1528_);
lean_inc(v_declHint_1515_);
v___x_1530_ = l_Lean_MessageData_ofConstName(v_declHint_1515_, v___x_1520_);
v_c_1531_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1531_, 0, v___x_1529_);
lean_ctor_set(v_c_1531_, 1, v___x_1530_);
v___x_1532_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1519_, v_declHint_1515_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec_ref(v_env_1519_);
lean_dec(v_declHint_1515_);
v___x_1533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v_c_1531_);
v___x_1535_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = l_Lean_MessageData_note(v___x_1536_);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_msg_1514_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
else
{
lean_object* v_val_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1575_; 
v_val_1540_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1542_ = v___x_1532_;
v_isShared_1543_ = v_isSharedCheck_1575_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_val_1540_);
lean_dec(v___x_1532_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1575_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v_mod_1547_; uint8_t v___x_1548_; 
v___x_1544_ = lean_box(0);
v___x_1545_ = l_Lean_Environment_header(v_env_1519_);
lean_dec_ref(v_env_1519_);
v___x_1546_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1545_);
v_mod_1547_ = lean_array_get(v___x_1544_, v___x_1546_, v_val_1540_);
lean_dec(v_val_1540_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = l_Lean_isPrivateName(v_declHint_1515_);
lean_dec(v_declHint_1515_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1549_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v_c_1531_);
v___x_1551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = l_Lean_MessageData_ofName(v_mod_1547_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = l_Lean_MessageData_note(v___x_1556_);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_msg_1514_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1558_);
v___x_1560_ = v___x_1542_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1562_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v_c_1531_);
v___x_1564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_MessageData_ofName(v_mod_1547_);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = l_Lean_MessageData_note(v___x_1569_);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_msg_1514_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1571_);
v___x_1573_ = v___x_1542_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1576_; 
lean_dec_ref(v_env_1519_);
lean_dec(v_declHint_1515_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_msg_1514_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___boxed(lean_object* v_msg_1577_, lean_object* v_declHint_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_1577_, v_declHint_1578_, v___y_1579_);
lean_dec(v___y_1579_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(lean_object* v_msg_1582_, lean_object* v_declHint_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1599_; 
v___x_1589_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_1582_, v_declHint_1583_, v___y_1587_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1594_ = l_Lean_unknownIdentifierMessageTag;
v___x_1595_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v_a_1590_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32___boxed(lean_object* v_msg_1600_, lean_object* v_declHint_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(v_msg_1600_, v_declHint_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(lean_object* v_ref_1608_, lean_object* v_msg_1609_, lean_object* v_declHint_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v_a_1617_; lean_object* v___x_1618_; 
v___x_1616_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(v_msg_1609_, v_declHint_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_1608_, v_a_1617_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg___boxed(lean_object* v_ref_1619_, lean_object* v_msg_1620_, lean_object* v_declHint_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_1619_, v_msg_1620_, v_declHint_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v_ref_1619_);
return v_res_1627_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0));
v___x_1630_ = l_Lean_stringToMessageData(v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(lean_object* v_ref_1631_, lean_object* v_constName_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1638_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1);
v___x_1639_ = 0;
lean_inc(v_constName_1632_);
v___x_1640_ = l_Lean_MessageData_ofConstName(v_constName_1632_, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1638_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_1631_, v___x_1643_, v_constName_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___boxed(lean_object* v_ref_1645_, lean_object* v_constName_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_1645_, v_constName_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v_ref_1645_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(lean_object* v_constName_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_ref_1659_; lean_object* v___x_1660_; 
v_ref_1659_ = lean_ctor_get(v___y_1656_, 2);
v___x_1660_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_1659_, v_constName_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg___boxed(lean_object* v_constName_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object* v_constName_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v_env_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; 
v___x_1674_ = lean_st_ref_get(v___y_1672_);
v_env_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc_ref(v_env_1675_);
lean_dec(v___x_1674_);
v___x_1676_ = 0;
lean_inc(v_constName_1668_);
v___x_1677_ = l_Lean_Environment_find_x3f(v_env_1675_, v_constName_1668_, v___x_1676_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1678_;
}
else
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec(v_constName_1668_);
v_val_1679_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1677_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v___x_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_val_1679_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object* v_constName_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_constName_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(lean_object* v_keys_1694_, lean_object* v_vals_1695_, lean_object* v_i_1696_, lean_object* v_k_1697_){
_start:
{
lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = lean_array_get_size(v_keys_1694_);
v___x_1699_ = lean_nat_dec_lt(v_i_1696_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
lean_dec(v_i_1696_);
v___x_1700_ = lean_box(0);
return v___x_1700_;
}
else
{
lean_object* v_k_x27_1701_; uint8_t v___x_1702_; 
v_k_x27_1701_ = lean_array_fget_borrowed(v_keys_1694_, v_i_1696_);
v___x_1702_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_k_1697_, v_k_x27_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_nat_add(v_i_1696_, v___x_1703_);
lean_dec(v_i_1696_);
v_i_1696_ = v___x_1704_;
goto _start;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_array_fget_borrowed(v_vals_1695_, v_i_1696_);
lean_dec(v_i_1696_);
lean_inc(v___x_1706_);
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
return v___x_1707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg___boxed(lean_object* v_keys_1708_, lean_object* v_vals_1709_, lean_object* v_i_1710_, lean_object* v_k_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_keys_1708_, v_vals_1709_, v_i_1710_, v_k_1711_);
lean_dec_ref(v_k_1711_);
lean_dec_ref(v_vals_1709_);
lean_dec_ref(v_keys_1708_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object* v_x_1713_, size_t v_x_1714_, lean_object* v_x_1715_){
_start:
{
if (lean_obj_tag(v_x_1713_) == 0)
{
lean_object* v_es_1716_; lean_object* v___x_1717_; size_t v___x_1718_; size_t v___x_1719_; lean_object* v_j_1720_; lean_object* v___x_1721_; 
v_es_1716_ = lean_ctor_get(v_x_1713_, 0);
v___x_1717_ = lean_box(2);
v___x_1718_ = ((size_t)31ULL);
v___x_1719_ = lean_usize_land(v_x_1714_, v___x_1718_);
v_j_1720_ = lean_usize_to_nat(v___x_1719_);
v___x_1721_ = lean_array_get_borrowed(v___x_1717_, v_es_1716_, v_j_1720_);
lean_dec(v_j_1720_);
switch(lean_obj_tag(v___x_1721_))
{
case 0:
{
lean_object* v_key_1722_; lean_object* v_val_1723_; uint8_t v___x_1724_; 
v_key_1722_ = lean_ctor_get(v___x_1721_, 0);
v_val_1723_ = lean_ctor_get(v___x_1721_, 1);
v___x_1724_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_1715_, v_key_1722_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_box(0);
return v___x_1725_;
}
else
{
lean_object* v___x_1726_; 
lean_inc(v_val_1723_);
v___x_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_val_1723_);
return v___x_1726_;
}
}
case 1:
{
lean_object* v_node_1727_; size_t v___x_1728_; size_t v___x_1729_; 
v_node_1727_ = lean_ctor_get(v___x_1721_, 0);
v___x_1728_ = ((size_t)5ULL);
v___x_1729_ = lean_usize_shift_right(v_x_1714_, v___x_1728_);
v_x_1713_ = v_node_1727_;
v_x_1714_ = v___x_1729_;
goto _start;
}
default: 
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_box(0);
return v___x_1731_;
}
}
}
else
{
lean_object* v_ks_1732_; lean_object* v_vs_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_ks_1732_ = lean_ctor_get(v_x_1713_, 0);
v_vs_1733_ = lean_ctor_get(v_x_1713_, 1);
v___x_1734_ = lean_unsigned_to_nat(0u);
v___x_1735_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_ks_1732_, v_vs_1733_, v___x_1734_, v_x_1715_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_x_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_){
_start:
{
size_t v_x_22885__boxed_1739_; lean_object* v_res_1740_; 
v_x_22885__boxed_1739_ = lean_unbox_usize(v_x_1737_);
lean_dec(v_x_1737_);
v_res_1740_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_1736_, v_x_22885__boxed_1739_, v_x_1738_);
lean_dec_ref(v_x_1738_);
lean_dec_ref(v_x_1736_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object* v_x_1741_, lean_object* v_x_1742_){
_start:
{
uint64_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_1742_);
v___x_1744_ = lean_uint64_to_usize(v___x_1743_);
v___x_1745_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_1741_, v___x_1744_, v_x_1742_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object* v_x_1746_, lean_object* v_x_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_1746_, v_x_1747_);
lean_dec_ref(v_x_1747_);
lean_dec_ref(v_x_1746_);
return v_res_1748_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__2(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1751_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6));
v___x_1752_ = lean_unsigned_to_nat(42u);
v___x_1753_ = lean_unsigned_to_nat(81u);
v___x_1754_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__1));
v___x_1755_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__0));
v___x_1756_ = l_mkPanicMessageWithDecl(v___x_1755_, v___x_1754_, v___x_1753_, v___x_1752_, v___x_1751_);
return v___x_1756_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__4(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__3));
v___x_1759_ = l_Lean_stringToMessageData(v___x_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__5(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0));
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0));
v___x_1762_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1761_, v___x_1760_);
return v___x_1762_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__9(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__8));
v___x_1768_ = l_Lean_stringToMessageData(v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object* v_indName_1769_, lean_object* v_ctors_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v___x_1776_; lean_object* v_env_1777_; lean_object* v___x_1778_; uint8_t v_isModule_1779_; lean_object* v___x_1780_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___x_2025_; uint8_t v___y_2027_; 
v___x_1776_ = lean_st_ref_get(v_a_1774_);
v_env_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc_ref(v_env_1777_);
lean_dec(v___x_1776_);
v___x_1778_ = l_Lean_Environment_header(v_env_1777_);
v_isModule_1779_ = lean_ctor_get_uint8(v___x_1778_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1778_);
v___x_1780_ = l_Lean_instInhabitedExpr;
v___x_2025_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__5, &l_Lean_Meta_mkSparseCasesOn___closed__5_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__5);
if (v_isModule_1779_ == 0)
{
v___y_2027_ = v_isModule_1779_;
goto v___jp_2026_;
}
else
{
uint8_t v_isExporting_2084_; 
v_isExporting_2084_ = lean_ctor_get_uint8(v_env_1777_, sizeof(void*)*8);
if (v_isExporting_2084_ == 0)
{
v___y_2027_ = v_isModule_1779_;
goto v___jp_2026_;
}
else
{
uint8_t v___x_2085_; 
v___x_2085_ = 0;
v___y_2027_ = v___x_2085_;
goto v___jp_2026_;
}
}
v___jp_1781_:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_ConstantInfo_levelParams(v___y_1789_);
if (lean_obj_tag(v___x_1799_) == 1)
{
lean_object* v_tail_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___f_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; lean_object* v___x_1806_; 
v_tail_1800_ = lean_ctor_get(v___x_1799_, 1);
lean_inc(v_tail_1800_);
v___x_1801_ = lean_box(0);
v___x_1802_ = l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(v_tail_1800_, v___x_1801_);
lean_inc_ref(v_ctors_1770_);
v___f_1803_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__2___boxed), 16, 9);
lean_closure_set(v___f_1803_, 0, v___y_1787_);
lean_closure_set(v___f_1803_, 1, v___x_1780_);
lean_closure_set(v___f_1803_, 2, v___y_1783_);
lean_closure_set(v___f_1803_, 3, v_ctors_1770_);
lean_closure_set(v___f_1803_, 4, v___y_1784_);
lean_closure_set(v___f_1803_, 5, v___x_1802_);
lean_closure_set(v___f_1803_, 6, v___y_1782_);
lean_closure_set(v___f_1803_, 7, v___y_1786_);
lean_closure_set(v___f_1803_, 8, v___y_1785_);
v___x_1804_ = l_Lean_ConstantInfo_type(v___y_1789_);
lean_dec_ref(v___y_1789_);
v___x_1805_ = 0;
v___x_1806_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v___x_1804_, v___f_1803_, v___x_1805_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1808_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc_n(v_a_1807_, 2);
lean_dec_ref_known(v___x_1806_, 1);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1797_);
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1795_);
v___x_1808_ = lean_infer_type(v_a_1807_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1958_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = lean_box(1);
lean_inc(v___y_1794_);
v___x_1811_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___y_1794_, v___x_1799_, v_a_1809_, v_a_1807_, v___x_1810_, v___y_1798_);
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1958_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1958_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 1);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_addDecl(v___x_1817_, v___x_1805_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1819_; lean_object* v_env_1820_; lean_object* v_nextMacroScope_1821_; lean_object* v_ngen_1822_; lean_object* v_auxDeclNGen_1823_; lean_object* v_traceState_1824_; lean_object* v_messages_1825_; lean_object* v_infoState_1826_; lean_object* v_snapshotTasks_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref_known(v___x_1818_, 1);
v___x_1819_ = lean_st_ref_take(v___y_1798_);
v_env_1820_ = lean_ctor_get(v___x_1819_, 0);
v_nextMacroScope_1821_ = lean_ctor_get(v___x_1819_, 1);
v_ngen_1822_ = lean_ctor_get(v___x_1819_, 2);
v_auxDeclNGen_1823_ = lean_ctor_get(v___x_1819_, 3);
v_traceState_1824_ = lean_ctor_get(v___x_1819_, 4);
v_messages_1825_ = lean_ctor_get(v___x_1819_, 6);
v_infoState_1826_ = lean_ctor_get(v___x_1819_, 7);
v_snapshotTasks_1827_ = lean_ctor_get(v___x_1819_, 8);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v___x_1819_, 5);
lean_dec(v_unused_1948_);
v___x_1829_ = v___x_1819_;
v_isShared_1830_ = v_isSharedCheck_1947_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snapshotTasks_1827_);
lean_inc(v_infoState_1826_);
lean_inc(v_messages_1825_);
lean_inc(v_traceState_1824_);
lean_inc(v_auxDeclNGen_1823_);
lean_inc(v_ngen_1822_);
lean_inc(v_nextMacroScope_1821_);
lean_inc(v_env_1820_);
lean_dec(v___x_1819_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1947_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_inc_ref(v___y_1793_);
v___x_1831_ = l_Lean_EnvExtension_modifyState___redArg(v___y_1793_, v_env_1820_, v___y_1791_, v___y_1790_, v___y_1788_);
v___x_1832_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 5, v___x_1832_);
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1834_ = v___x_1829_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_nextMacroScope_1821_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_ngen_1822_);
lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_auxDeclNGen_1823_);
lean_ctor_set(v_reuseFailAlloc_1946_, 4, v_traceState_1824_);
lean_ctor_set(v_reuseFailAlloc_1946_, 5, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1946_, 6, v_messages_1825_);
lean_ctor_set(v_reuseFailAlloc_1946_, 7, v_infoState_1826_);
lean_ctor_set(v_reuseFailAlloc_1946_, 8, v_snapshotTasks_1827_);
v___x_1834_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_mctx_1837_; lean_object* v_zetaDeltaFVarIds_1838_; lean_object* v_postponed_1839_; lean_object* v_diag_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1944_; 
v___x_1835_ = lean_st_ref_put(v___y_1798_, v___x_1834_);
v___x_1836_ = lean_st_ref_take(v___y_1796_);
v_mctx_1837_ = lean_ctor_get(v___x_1836_, 0);
v_zetaDeltaFVarIds_1838_ = lean_ctor_get(v___x_1836_, 2);
v_postponed_1839_ = lean_ctor_get(v___x_1836_, 3);
v_diag_1840_ = lean_ctor_get(v___x_1836_, 4);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v___x_1836_, 1);
lean_dec(v_unused_1945_);
v___x_1842_ = v___x_1836_;
v_isShared_1843_ = v_isSharedCheck_1944_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_diag_1840_);
lean_inc(v_postponed_1839_);
lean_inc(v_zetaDeltaFVarIds_1838_);
lean_inc(v_mctx_1837_);
lean_dec(v___x_1836_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1944_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1844_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 1, v___x_1844_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_mctx_1837_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_zetaDeltaFVarIds_1838_);
lean_ctor_set(v_reuseFailAlloc_1943_, 3, v_postponed_1839_);
lean_ctor_set(v_reuseFailAlloc_1943_, 4, v_diag_1840_);
v___x_1846_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_env_1850_; lean_object* v_nextMacroScope_1851_; lean_object* v_ngen_1852_; lean_object* v_auxDeclNGen_1853_; lean_object* v_traceState_1854_; lean_object* v_messages_1855_; lean_object* v_infoState_1856_; lean_object* v_snapshotTasks_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1941_; 
v___x_1847_ = lean_st_ref_put(v___y_1796_, v___x_1846_);
lean_inc(v___y_1794_);
v___x_1848_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec_ref(v___x_1848_);
v___x_1849_ = lean_st_ref_take(v___y_1798_);
v_env_1850_ = lean_ctor_get(v___x_1849_, 0);
v_nextMacroScope_1851_ = lean_ctor_get(v___x_1849_, 1);
v_ngen_1852_ = lean_ctor_get(v___x_1849_, 2);
v_auxDeclNGen_1853_ = lean_ctor_get(v___x_1849_, 3);
v_traceState_1854_ = lean_ctor_get(v___x_1849_, 4);
v_messages_1855_ = lean_ctor_get(v___x_1849_, 6);
v_infoState_1856_ = lean_ctor_get(v___x_1849_, 7);
v_snapshotTasks_1857_ = lean_ctor_get(v___x_1849_, 8);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v___x_1849_, 5);
lean_dec(v_unused_1942_);
v___x_1859_ = v___x_1849_;
v_isShared_1860_ = v_isSharedCheck_1941_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_snapshotTasks_1857_);
lean_inc(v_infoState_1856_);
lean_inc(v_messages_1855_);
lean_inc(v_traceState_1854_);
lean_inc(v_auxDeclNGen_1853_);
lean_inc(v_ngen_1852_);
lean_inc(v_nextMacroScope_1851_);
lean_inc(v_env_1850_);
lean_dec(v___x_1849_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1941_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_inc(v___y_1794_);
v___x_1861_ = l_Lean_markSparseCasesOn(v_env_1850_, v___y_1794_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 5, v___x_1832_);
lean_ctor_set(v___x_1859_, 0, v___x_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_nextMacroScope_1851_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_ngen_1852_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_auxDeclNGen_1853_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_traceState_1854_);
lean_ctor_set(v_reuseFailAlloc_1940_, 5, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1940_, 6, v_messages_1855_);
lean_ctor_set(v_reuseFailAlloc_1940_, 7, v_infoState_1856_);
lean_ctor_set(v_reuseFailAlloc_1940_, 8, v_snapshotTasks_1857_);
v___x_1863_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v_mctx_1866_; lean_object* v_zetaDeltaFVarIds_1867_; lean_object* v_postponed_1868_; lean_object* v_diag_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1938_; 
v___x_1864_ = lean_st_ref_put(v___y_1798_, v___x_1863_);
v___x_1865_ = lean_st_ref_take(v___y_1796_);
v_mctx_1866_ = lean_ctor_get(v___x_1865_, 0);
v_zetaDeltaFVarIds_1867_ = lean_ctor_get(v___x_1865_, 2);
v_postponed_1868_ = lean_ctor_get(v___x_1865_, 3);
v_diag_1869_ = lean_ctor_get(v___x_1865_, 4);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v___x_1865_, 1);
lean_dec(v_unused_1939_);
v___x_1871_ = v___x_1865_;
v_isShared_1872_ = v_isSharedCheck_1938_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_diag_1869_);
lean_inc(v_postponed_1868_);
lean_inc(v_zetaDeltaFVarIds_1867_);
lean_inc(v_mctx_1866_);
lean_dec(v___x_1865_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1938_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 1, v___x_1844_);
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_mctx_1866_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_zetaDeltaFVarIds_1867_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v_postponed_1868_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v_diag_1869_);
v___x_1874_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v_env_1877_; lean_object* v_nextMacroScope_1878_; lean_object* v_ngen_1879_; lean_object* v_auxDeclNGen_1880_; lean_object* v_traceState_1881_; lean_object* v_messages_1882_; lean_object* v_infoState_1883_; lean_object* v_snapshotTasks_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1935_; 
v___x_1875_ = lean_st_ref_put(v___y_1796_, v___x_1874_);
v___x_1876_ = lean_st_ref_take(v___y_1798_);
v_env_1877_ = lean_ctor_get(v___x_1876_, 0);
v_nextMacroScope_1878_ = lean_ctor_get(v___x_1876_, 1);
v_ngen_1879_ = lean_ctor_get(v___x_1876_, 2);
v_auxDeclNGen_1880_ = lean_ctor_get(v___x_1876_, 3);
v_traceState_1881_ = lean_ctor_get(v___x_1876_, 4);
v_messages_1882_ = lean_ctor_get(v___x_1876_, 6);
v_infoState_1883_ = lean_ctor_get(v___x_1876_, 7);
v_snapshotTasks_1884_ = lean_ctor_get(v___x_1876_, 8);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; 
v_unused_1936_ = lean_ctor_get(v___x_1876_, 5);
lean_dec(v_unused_1936_);
v___x_1886_ = v___x_1876_;
v_isShared_1887_ = v_isSharedCheck_1935_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_snapshotTasks_1884_);
lean_inc(v_infoState_1883_);
lean_inc(v_messages_1882_);
lean_inc(v_traceState_1881_);
lean_inc(v_auxDeclNGen_1880_);
lean_inc(v_ngen_1879_);
lean_inc(v_nextMacroScope_1878_);
lean_inc(v_env_1877_);
lean_dec(v___x_1876_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1935_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_numParams_1888_; lean_object* v_numIndices_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v_numParams_1888_ = lean_ctor_get(v___y_1792_, 1);
lean_inc(v_numParams_1888_);
v_numIndices_1889_ = lean_ctor_get(v___y_1792_, 2);
lean_inc(v_numIndices_1889_);
lean_dec_ref(v___y_1792_);
v___x_1890_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = lean_nat_add(v_numParams_1888_, v___x_1891_);
lean_dec(v_numParams_1888_);
v___x_1893_ = lean_nat_add(v___x_1892_, v_numIndices_1889_);
lean_dec(v_numIndices_1889_);
lean_dec(v___x_1892_);
v___x_1894_ = lean_nat_add(v___x_1893_, v___x_1891_);
v___x_1895_ = lean_array_get_size(v_ctors_1770_);
v___x_1896_ = lean_nat_add(v___x_1894_, v___x_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_nat_add(v___x_1896_, v___x_1891_);
lean_dec(v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1898_, 0, v_indName_1769_);
lean_ctor_set(v___x_1898_, 1, v___x_1893_);
lean_ctor_set(v___x_1898_, 2, v___x_1897_);
lean_ctor_set(v___x_1898_, 3, v_ctors_1770_);
lean_inc(v___y_1794_);
v___x_1899_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1890_, v_env_1877_, v___y_1794_, v___x_1898_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 5, v___x_1832_);
lean_ctor_set(v___x_1886_, 0, v___x_1899_);
v___x_1901_ = v___x_1886_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_nextMacroScope_1878_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_ngen_1879_);
lean_ctor_set(v_reuseFailAlloc_1934_, 3, v_auxDeclNGen_1880_);
lean_ctor_set(v_reuseFailAlloc_1934_, 4, v_traceState_1881_);
lean_ctor_set(v_reuseFailAlloc_1934_, 5, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1934_, 6, v_messages_1882_);
lean_ctor_set(v_reuseFailAlloc_1934_, 7, v_infoState_1883_);
lean_ctor_set(v_reuseFailAlloc_1934_, 8, v_snapshotTasks_1884_);
v___x_1901_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_mctx_1904_; lean_object* v_zetaDeltaFVarIds_1905_; lean_object* v_postponed_1906_; lean_object* v_diag_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1932_; 
v___x_1902_ = lean_st_ref_put(v___y_1798_, v___x_1901_);
v___x_1903_ = lean_st_ref_take(v___y_1796_);
v_mctx_1904_ = lean_ctor_get(v___x_1903_, 0);
v_zetaDeltaFVarIds_1905_ = lean_ctor_get(v___x_1903_, 2);
v_postponed_1906_ = lean_ctor_get(v___x_1903_, 3);
v_diag_1907_ = lean_ctor_get(v___x_1903_, 4);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1903_, 1);
lean_dec(v_unused_1933_);
v___x_1909_ = v___x_1903_;
v_isShared_1910_ = v_isSharedCheck_1932_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_diag_1907_);
lean_inc(v_postponed_1906_);
lean_inc(v_zetaDeltaFVarIds_1905_);
lean_inc(v_mctx_1904_);
lean_dec(v___x_1903_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1932_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v___x_1844_);
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_mctx_1904_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_zetaDeltaFVarIds_1905_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_postponed_1906_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_diag_1907_);
v___x_1912_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_st_ref_put(v___y_1796_, v___x_1912_);
lean_inc(v___y_1794_);
v___x_1914_ = l_Lean_enableRealizationsForConst(v___y_1794_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v___x_1914_, 0);
lean_dec(v_unused_1922_);
v___x_1916_ = v___x_1914_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_dec(v___x_1914_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___y_1794_);
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___y_1794_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v___y_1794_);
v_a_1923_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1914_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1914_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
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
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1788_);
lean_dec_ref(v_ctors_1770_);
lean_dec(v_indName_1769_);
v_a_1949_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1818_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1818_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_a_1807_);
lean_dec_ref_known(v___x_1799_, 2);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1788_);
lean_dec_ref(v_ctors_1770_);
lean_dec(v_indName_1769_);
v_a_1959_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1808_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1808_);
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
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref_known(v___x_1799_, 2);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1788_);
lean_dec_ref(v_ctors_1770_);
lean_dec(v_indName_1769_);
v_a_1967_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1806_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1806_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_dec(v___x_1799_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v_ctors_1770_);
lean_dec(v_indName_1769_);
v___x_1975_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__2, &l_Lean_Meta_mkSparseCasesOn___closed__2_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__2);
v___x_1976_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(v___x_1975_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
return v___x_1976_;
}
}
v___jp_1977_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_inc(v_indName_1769_);
v___x_1991_ = l_Lean_mkCasesOnName(v_indName_1769_);
lean_inc(v___x_1991_);
v___x_1992_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(v___x_1991_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_toConstantVal_1993_; lean_object* v_a_1994_; lean_object* v_levelParams_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v_toConstantVal_1993_ = lean_ctor_get(v___y_1984_, 0);
v_a_1994_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1992_, 1);
v_levelParams_1995_ = lean_ctor_get(v_toConstantVal_1993_, 1);
lean_inc(v_indName_1769_);
v___x_1996_ = l_Lean_mkCtorIdxName(v_indName_1769_);
v___x_1997_ = l_Lean_ConstantInfo_levelParams(v_a_1994_);
v___x_1998_ = l_List_lengthTR___redArg(v___x_1997_);
lean_dec(v___x_1997_);
v___x_1999_ = l_List_lengthTR___redArg(v_levelParams_1995_);
v___x_2000_ = lean_unsigned_to_nat(1u);
v___x_2001_ = lean_nat_add(v___x_1999_, v___x_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_nat_dec_eq(v___x_1998_, v___x_2001_);
lean_dec(v___x_2001_);
lean_dec(v___x_1998_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v___x_1996_);
lean_dec(v_a_1994_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v_ctors_1770_);
lean_dec(v_indName_1769_);
v___x_2003_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__4, &l_Lean_Meta_mkSparseCasesOn___closed__4_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__4);
v___x_2004_ = l_Lean_MessageData_ofConstName(v___x_1991_, v___x_2002_);
v___x_2005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_2007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2005_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_2007_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
else
{
lean_inc(v_a_1994_);
v___y_1782_ = v_a_1994_;
v___y_1783_ = v___y_1978_;
v___y_1784_ = v___x_1996_;
v___y_1785_ = v___x_1991_;
v___y_1786_ = v___y_1980_;
v___y_1787_ = v___y_1981_;
v___y_1788_ = v___y_1982_;
v___y_1789_ = v_a_1994_;
v___y_1790_ = v___y_1983_;
v___y_1791_ = v___y_1979_;
v___y_1792_ = v___y_1984_;
v___y_1793_ = v___y_1985_;
v___y_1794_ = v___y_1986_;
v___y_1795_ = v___y_1987_;
v___y_1796_ = v___y_1988_;
v___y_1797_ = v___y_1989_;
v___y_1798_ = v___y_1990_;
goto v___jp_1781_;
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v___x_1991_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v_ctors_1770_);
lean_dec(v_indName_1769_);
v_a_2017_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1992_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1992_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
v___jp_2026_:
{
lean_object* v___x_2028_; lean_object* v_asyncMode_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2028_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
v_asyncMode_2029_ = lean_ctor_get(v___x_2028_, 2);
lean_inc_ref(v_ctors_1770_);
lean_inc(v_indName_1769_);
v___x_2030_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2030_, 0, v_indName_1769_);
lean_ctor_set(v___x_2030_, 1, v_ctors_1770_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*2, v___y_2027_);
v___x_2031_ = lean_box(0);
v___x_2032_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2025_, v___x_2028_, v_env_1777_, v_asyncMode_2029_, v___x_2031_);
v___x_2033_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v___x_2032_, v___x_2030_);
lean_dec(v___x_2032_);
if (lean_obj_tag(v___x_2033_) == 1)
{
lean_object* v_val_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref_known(v___x_2030_, 2);
lean_dec_ref(v_ctors_1770_);
lean_dec(v_indName_1769_);
v_val_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_val_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 0);
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_val_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v_a_2044_; lean_object* v___x_2045_; 
lean_dec(v___x_2033_);
v___x_2042_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__7));
v___x_2043_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v___x_2042_, v_a_1774_);
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___x_2043_);
lean_inc(v_indName_1769_);
v___x_2045_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(v_indName_1769_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; size_t v_sz_2048_; size_t v___x_2049_; lean_object* v___x_2050_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = lean_box(0);
v_sz_2048_ = lean_array_size(v_ctors_1770_);
v___x_2049_ = ((size_t)0ULL);
lean_inc(v_indName_1769_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_2046_, v_indName_1769_, v_ctors_1770_, v_sz_2048_, v___x_2049_, v___x_2047_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_numParams_2051_; lean_object* v_numIndices_2052_; lean_object* v_ctors_2053_; lean_object* v___f_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
lean_dec_ref_known(v___x_2050_, 1);
v_numParams_2051_ = lean_ctor_get(v_a_2046_, 1);
lean_inc(v_numParams_2051_);
v_numIndices_2052_ = lean_ctor_get(v_a_2046_, 2);
lean_inc(v_numIndices_2052_);
v_ctors_2053_ = lean_ctor_get(v_a_2046_, 4);
lean_inc(v_ctors_2053_);
lean_inc(v_a_2044_);
v___f_2054_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__0), 3, 2);
lean_closure_set(v___f_2054_, 0, v___x_2030_);
lean_closure_set(v___f_2054_, 1, v_a_2044_);
v___x_2055_ = lean_array_get_size(v_ctors_1770_);
v___x_2056_ = l_List_lengthTR___redArg(v_ctors_2053_);
v___x_2057_ = lean_nat_dec_eq(v___x_2055_, v___x_2056_);
lean_dec(v___x_2056_);
if (v___x_2057_ == 0)
{
v___y_1978_ = v_numIndices_2052_;
v___y_1979_ = v___f_2054_;
v___y_1980_ = v_ctors_2053_;
v___y_1981_ = v_numParams_2051_;
v___y_1982_ = v___x_2031_;
v___y_1983_ = v_asyncMode_2029_;
v___y_1984_ = v_a_2046_;
v___y_1985_ = v___x_2028_;
v___y_1986_ = v_a_2044_;
v___y_1987_ = v_a_1771_;
v___y_1988_ = v_a_1772_;
v___y_1989_ = v_a_1773_;
v___y_1990_ = v_a_1774_;
goto v___jp_1977_;
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v___f_2054_);
lean_dec(v_ctors_2053_);
lean_dec(v_numIndices_2052_);
lean_dec(v_numParams_2051_);
lean_dec(v_a_2046_);
lean_dec(v_a_2044_);
lean_dec_ref(v_ctors_1770_);
lean_dec(v_indName_1769_);
v___x_2058_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__9, &l_Lean_Meta_mkSparseCasesOn___closed__9_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__9);
v___x_2059_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_2058_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_2046_);
lean_dec(v_a_2044_);
lean_dec_ref_known(v___x_2030_, 2);
lean_dec_ref(v_ctors_1770_);
lean_dec(v_indName_1769_);
v_a_2068_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2050_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2050_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_a_2044_);
lean_dec_ref_known(v___x_2030_, 2);
lean_dec_ref(v_ctors_1770_);
lean_dec(v_indName_1769_);
v_a_2076_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2045_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2045_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object* v_indName_2086_, lean_object* v_ctors_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Meta_mkSparseCasesOn(v_indName_2086_, v_ctors_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object* v_00_u03b2_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_2095_, v_x_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object* v_00_u03b2_2098_, lean_object* v_x_2099_, lean_object* v_x_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(v_00_u03b2_2098_, v_x_2099_, v_x_2100_);
lean_dec_ref(v_x_2100_);
lean_dec_ref(v_x_2099_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object* v_00_u03b2_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_x_2103_, v_x_2104_, v_x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(lean_object* v_00_u03b1_2107_, lean_object* v_name_2108_, uint8_t v_bi_2109_, lean_object* v_type_2110_, lean_object* v_k_2111_, uint8_t v_kind_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_2108_, v_bi_2109_, v_type_2110_, v_k_2111_, v_kind_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___boxed(lean_object* v_00_u03b1_2119_, lean_object* v_name_2120_, lean_object* v_bi_2121_, lean_object* v_type_2122_, lean_object* v_k_2123_, lean_object* v_kind_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
uint8_t v_bi_boxed_2130_; uint8_t v_kind_boxed_2131_; lean_object* v_res_2132_; 
v_bi_boxed_2130_ = lean_unbox(v_bi_2121_);
v_kind_boxed_2131_ = lean_unbox(v_kind_2124_);
v_res_2132_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(v_00_u03b1_2119_, v_name_2120_, v_bi_boxed_2130_, v_type_2122_, v_k_2123_, v_kind_boxed_2131_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(lean_object* v_00_u03b1_2133_, lean_object* v_name_2134_, lean_object* v_type_2135_, lean_object* v_k_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v_name_2134_, v_type_2135_, v_k_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object* v_00_u03b1_2143_, lean_object* v_name_2144_, lean_object* v_type_2145_, lean_object* v_k_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_00_u03b1_2143_, v_name_2144_, v_type_2145_, v_k_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object* v_00_u03b1_2153_, lean_object* v_msg_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object* v_00_u03b1_2161_, lean_object* v_msg_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_00_u03b1_2161_, v_msg_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(lean_object* v_declName_2169_, uint8_t v_s_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_2169_, v_s_2170_, v___y_2172_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___boxed(lean_object* v_declName_2177_, lean_object* v_s_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v_s_boxed_2184_; lean_object* v_res_2185_; 
v_s_boxed_2184_ = lean_unbox(v_s_2178_);
v_res_2185_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(v_declName_2177_, v_s_boxed_2184_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object* v_00_u03b2_2186_, lean_object* v_x_2187_, size_t v_x_2188_, lean_object* v_x_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_2187_, v_x_2188_, v_x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_){
_start:
{
size_t v_x_23653__boxed_2195_; lean_object* v_res_2196_; 
v_x_23653__boxed_2195_ = lean_unbox_usize(v_x_2193_);
lean_dec(v_x_2193_);
v_res_2196_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(v_00_u03b2_2191_, v_x_2192_, v_x_23653__boxed_2195_, v_x_2194_);
lean_dec_ref(v_x_2194_);
lean_dec_ref(v_x_2192_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object* v_00_u03b2_2197_, lean_object* v_x_2198_, size_t v_x_2199_, size_t v_x_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_2198_, v_x_2199_, v_x_2200_, v_x_2201_, v_x_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2204_, lean_object* v_x_2205_, lean_object* v_x_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
size_t v_x_23664__boxed_2210_; size_t v_x_23665__boxed_2211_; lean_object* v_res_2212_; 
v_x_23664__boxed_2210_ = lean_unbox_usize(v_x_2206_);
lean_dec(v_x_2206_);
v_x_23665__boxed_2211_ = lean_unbox_usize(v_x_2207_);
lean_dec(v_x_2207_);
v_res_2212_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(v_00_u03b2_2204_, v_x_2205_, v_x_23664__boxed_2210_, v_x_23665__boxed_2211_, v_x_2208_, v_x_2209_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(lean_object* v_00_u03b1_2213_, lean_object* v_constName_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2221_, lean_object* v_constName_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(v_00_u03b1_2221_, v_constName_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2229_, lean_object* v_keys_2230_, lean_object* v_vals_2231_, lean_object* v_heq_2232_, lean_object* v_i_2233_, lean_object* v_k_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_keys_2230_, v_vals_2231_, v_i_2233_, v_k_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___boxed(lean_object* v_00_u03b2_2236_, lean_object* v_keys_2237_, lean_object* v_vals_2238_, lean_object* v_heq_2239_, lean_object* v_i_2240_, lean_object* v_k_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(v_00_u03b2_2236_, v_keys_2237_, v_vals_2238_, v_heq_2239_, v_i_2240_, v_k_2241_);
lean_dec_ref(v_k_2241_);
lean_dec_ref(v_vals_2238_);
lean_dec_ref(v_keys_2237_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2243_, lean_object* v_n_2244_, lean_object* v_k_2245_, lean_object* v_v_2246_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(v_n_2244_, v_k_2245_, v_v_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2248_, size_t v_depth_2249_, lean_object* v_keys_2250_, lean_object* v_vals_2251_, lean_object* v_heq_2252_, lean_object* v_i_2253_, lean_object* v_entries_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_depth_2249_, v_keys_2250_, v_vals_2251_, v_i_2253_, v_entries_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___boxed(lean_object* v_00_u03b2_2256_, lean_object* v_depth_2257_, lean_object* v_keys_2258_, lean_object* v_vals_2259_, lean_object* v_heq_2260_, lean_object* v_i_2261_, lean_object* v_entries_2262_){
_start:
{
size_t v_depth_boxed_2263_; lean_object* v_res_2264_; 
v_depth_boxed_2263_ = lean_unbox_usize(v_depth_2257_);
lean_dec(v_depth_2257_);
v_res_2264_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(v_00_u03b2_2256_, v_depth_boxed_2263_, v_keys_2258_, v_vals_2259_, v_heq_2260_, v_i_2261_, v_entries_2262_);
lean_dec_ref(v_vals_2259_);
lean_dec_ref(v_keys_2258_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(lean_object* v_00_u03b1_2265_, lean_object* v_ref_2266_, lean_object* v_constName_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_2266_, v_constName_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___boxed(lean_object* v_00_u03b1_2274_, lean_object* v_ref_2275_, lean_object* v_constName_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(v_00_u03b1_2274_, v_ref_2275_, v_constName_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v_ref_2275_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26(lean_object* v_00_u03b2_2283_, lean_object* v_x_2284_, lean_object* v_x_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(v_x_2284_, v_x_2285_, v_x_2286_, v_x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(lean_object* v_00_u03b1_2289_, lean_object* v_ref_2290_, lean_object* v_msg_2291_, lean_object* v_declHint_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_2290_, v_msg_2291_, v_declHint_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___boxed(lean_object* v_00_u03b1_2299_, lean_object* v_ref_2300_, lean_object* v_msg_2301_, lean_object* v_declHint_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(v_00_u03b1_2299_, v_ref_2300_, v_msg_2301_, v_declHint_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v_ref_2300_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(lean_object* v_msg_2309_, lean_object* v_declHint_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_2309_, v_declHint_2310_, v___y_2314_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___boxed(lean_object* v_msg_2317_, lean_object* v_declHint_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(v_msg_2317_, v_declHint_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(lean_object* v_00_u03b1_2325_, lean_object* v_ref_2326_, lean_object* v_msg_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_2326_, v_msg_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___boxed(lean_object* v_00_u03b1_2334_, lean_object* v_ref_2335_, lean_object* v_msg_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(v_00_u03b1_2334_, v_ref_2335_, v_msg_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v_ref_2335_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object* v_env_2343_, lean_object* v_sparseCasesOnName_2344_){
_start:
{
lean_object* v___x_2345_; lean_object* v_toEnvExtension_2346_; lean_object* v_asyncMode_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; 
v___x_2345_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2346_ = lean_ctor_get(v___x_2345_, 0);
v_asyncMode_2347_ = lean_ctor_get(v_toEnvExtension_2346_, 2);
v___x_2348_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2349_ = 0;
v___x_2350_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2348_, v___x_2345_, v_env_2343_, v_sparseCasesOnName_2344_, v_asyncMode_2347_, v___x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object* v_sparseCasesOnName_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v_env_2355_; lean_object* v___x_2356_; lean_object* v_toEnvExtension_2357_; lean_object* v_asyncMode_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2354_ = lean_st_ref_get(v_a_2352_);
v_env_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc_ref(v_env_2355_);
lean_dec(v___x_2354_);
v___x_2356_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2357_ = lean_ctor_get(v___x_2356_, 0);
v_asyncMode_2358_ = lean_ctor_get(v_toEnvExtension_2357_, 2);
v___x_2359_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2360_ = 0;
v___x_2361_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2359_, v___x_2356_, v_env_2355_, v_sparseCasesOnName_2351_, v_asyncMode_2358_, v___x_2360_);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object* v_sparseCasesOnName_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2363_, v_a_2364_);
lean_dec(v_a_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object* v_sparseCasesOnName_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2367_, v_a_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object* v_sparseCasesOnName_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Meta_getSparseCasesOnInfo(v_sparseCasesOnName_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
return v_res_2376_;
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
