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
lean_object* v___f_392_; lean_object* v___x_16840__overap_393_; lean_object* v___x_394_; 
v___f_392_ = ((lean_object*)(l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0));
v___x_16840__overap_393_ = lean_panic_fn_borrowed(v___f_392_, v_msg_386_);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
v___x_394_ = lean_apply_5(v___x_16840__overap_393_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, lean_box(0));
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
size_t v_x_20952__boxed_541_; size_t v_x_20953__boxed_542_; lean_object* v_res_543_; 
v_x_20952__boxed_541_ = lean_unbox_usize(v_x_537_);
lean_dec(v_x_537_);
v_x_20953__boxed_542_ = lean_unbox_usize(v_x_538_);
lean_dec(v_x_538_);
v_res_543_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_536_, v_x_20952__boxed_541_, v_x_20953__boxed_542_, v_x_539_, v_x_540_);
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
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_17119__overap_642_; lean_object* v___x_643_; 
v___x_640_ = lean_box(0);
v___x_641_ = l_instInhabitedOfMonad___redArg(v___x_639_, v___x_640_);
v___x_17119__overap_642_ = lean_panic_fn_borrowed(v___x_641_, v_msg_585_);
lean_dec(v___x_641_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
v___x_643_ = lean_apply_5(v___x_17119__overap_642_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, lean_box(0));
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
v_options_674_ = lean_ctor_get(v___y_666_, 1);
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
v_ref_691_ = lean_ctor_get(v___y_688_, 4);
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
uint8_t v___x_21610__boxed_923_; uint8_t v___x_21611__boxed_924_; lean_object* v_res_925_; 
v___x_21610__boxed_923_ = lean_unbox(v___x_913_);
v___x_21611__boxed_924_ = lean_unbox(v___x_914_);
v_res_925_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(v_ctors_909_, v_a_910_, v___x_911_, v_a_912_, v___x_21610__boxed_923_, v___x_21611__boxed_924_, v_a_915_, v_ys_916_, v_x_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
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
lean_object* v_toCold_1457_; lean_object* v_options_1458_; lean_object* v_currRecDepth_1459_; lean_object* v_maxRecDepth_1460_; lean_object* v_ref_1461_; lean_object* v_currNamespace_1462_; lean_object* v_openDecls_1463_; lean_object* v_initHeartbeats_1464_; lean_object* v_maxHeartbeats_1465_; lean_object* v_currMacroScope_1466_; uint8_t v_diag_1467_; uint8_t v_suppressElabErrors_1468_; lean_object* v_ref_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_toCold_1457_ = lean_ctor_get(v___y_1454_, 0);
v_options_1458_ = lean_ctor_get(v___y_1454_, 1);
v_currRecDepth_1459_ = lean_ctor_get(v___y_1454_, 2);
v_maxRecDepth_1460_ = lean_ctor_get(v___y_1454_, 3);
v_ref_1461_ = lean_ctor_get(v___y_1454_, 4);
v_currNamespace_1462_ = lean_ctor_get(v___y_1454_, 5);
v_openDecls_1463_ = lean_ctor_get(v___y_1454_, 6);
v_initHeartbeats_1464_ = lean_ctor_get(v___y_1454_, 7);
v_maxHeartbeats_1465_ = lean_ctor_get(v___y_1454_, 8);
v_currMacroScope_1466_ = lean_ctor_get(v___y_1454_, 9);
v_diag_1467_ = lean_ctor_get_uint8(v___y_1454_, sizeof(void*)*10);
v_suppressElabErrors_1468_ = lean_ctor_get_uint8(v___y_1454_, sizeof(void*)*10 + 1);
v_ref_1469_ = l_Lean_replaceRef(v_ref_1450_, v_ref_1461_);
lean_inc(v_currMacroScope_1466_);
lean_inc(v_maxHeartbeats_1465_);
lean_inc(v_initHeartbeats_1464_);
lean_inc(v_openDecls_1463_);
lean_inc(v_currNamespace_1462_);
lean_inc(v_maxRecDepth_1460_);
lean_inc(v_currRecDepth_1459_);
lean_inc_ref(v_options_1458_);
lean_inc_ref(v_toCold_1457_);
v___x_1470_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1470_, 0, v_toCold_1457_);
lean_ctor_set(v___x_1470_, 1, v_options_1458_);
lean_ctor_set(v___x_1470_, 2, v_currRecDepth_1459_);
lean_ctor_set(v___x_1470_, 3, v_maxRecDepth_1460_);
lean_ctor_set(v___x_1470_, 4, v_ref_1469_);
lean_ctor_set(v___x_1470_, 5, v_currNamespace_1462_);
lean_ctor_set(v___x_1470_, 6, v_openDecls_1463_);
lean_ctor_set(v___x_1470_, 7, v_initHeartbeats_1464_);
lean_ctor_set(v___x_1470_, 8, v_maxHeartbeats_1465_);
lean_ctor_set(v___x_1470_, 9, v_currMacroScope_1466_);
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*10, v_diag_1467_);
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*10 + 1, v_suppressElabErrors_1468_);
v___x_1471_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_1451_, v___y_1452_, v___y_1453_, v___x_1470_, v___y_1455_);
lean_dec_ref_known(v___x_1470_, 10);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg___boxed(lean_object* v_ref_1472_, lean_object* v_msg_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_1472_, v_msg_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v_ref_1472_);
return v_res_1479_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0(void){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1);
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
lean_ctor_set(v___x_1485_, 3, v___x_1484_);
lean_ctor_set(v___x_1485_, 4, v___x_1483_);
lean_ctor_set(v___x_1485_, 5, v___x_1483_);
lean_ctor_set(v___x_1485_, 6, v___x_1483_);
lean_ctor_set(v___x_1485_, 7, v___x_1483_);
lean_ctor_set(v___x_1485_, 8, v___x_1483_);
lean_ctor_set(v___x_1485_, 9, v___x_1483_);
lean_ctor_set(v___x_1485_, 10, v___x_1483_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = lean_unsigned_to_nat(32u);
v___x_1487_ = lean_mk_empty_array_with_capacity(v___x_1486_);
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4(void){
_start:
{
size_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1489_ = ((size_t)5ULL);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = lean_unsigned_to_nat(32u);
v___x_1492_ = lean_mk_empty_array_with_capacity(v___x_1491_);
v___x_1493_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3);
v___x_1494_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___x_1492_);
lean_ctor_set(v___x_1494_, 2, v___x_1490_);
lean_ctor_set(v___x_1494_, 3, v___x_1490_);
lean_ctor_set_usize(v___x_1494_, 4, v___x_1489_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1495_ = lean_box(1);
v___x_1496_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4);
v___x_1497_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1);
v___x_1498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v___x_1496_);
lean_ctor_set(v___x_1498_, 2, v___x_1495_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6));
v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12));
v___x_1510_ = l_Lean_stringToMessageData(v___x_1509_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14));
v___x_1513_ = l_Lean_stringToMessageData(v___x_1512_);
return v___x_1513_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16));
v___x_1516_ = l_Lean_stringToMessageData(v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18));
v___x_1519_ = l_Lean_stringToMessageData(v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(lean_object* v_msg_1520_, lean_object* v_declHint_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; lean_object* v_env_1525_; uint8_t v___x_1526_; 
v___x_1524_ = lean_st_ref_get(v___y_1522_);
v_env_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc_ref(v_env_1525_);
lean_dec(v___x_1524_);
v___x_1526_ = l_Lean_Name_isAnonymous(v_declHint_1521_);
if (v___x_1526_ == 0)
{
uint8_t v_isExporting_1527_; 
v_isExporting_1527_ = lean_ctor_get_uint8(v_env_1525_, sizeof(void*)*8);
if (v_isExporting_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_dec_ref(v_env_1525_);
lean_dec(v_declHint_1521_);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_msg_1520_);
return v___x_1528_;
}
else
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
lean_inc_ref(v_env_1525_);
v___x_1529_ = l_Lean_Environment_setExporting(v_env_1525_, v___x_1526_);
lean_inc(v_declHint_1521_);
lean_inc_ref(v___x_1529_);
v___x_1530_ = l_Lean_Environment_contains(v___x_1529_, v_declHint_1521_, v_isExporting_1527_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_dec_ref(v___x_1529_);
lean_dec_ref(v_env_1525_);
lean_dec(v_declHint_1521_);
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_msg_1520_);
return v___x_1531_;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_c_1537_; lean_object* v___x_1538_; 
v___x_1532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2);
v___x_1533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5);
v___x_1534_ = l_Lean_Options_empty;
v___x_1535_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1529_);
lean_ctor_set(v___x_1535_, 1, v___x_1532_);
lean_ctor_set(v___x_1535_, 2, v___x_1533_);
lean_ctor_set(v___x_1535_, 3, v___x_1534_);
lean_inc(v_declHint_1521_);
v___x_1536_ = l_Lean_MessageData_ofConstName(v_declHint_1521_, v___x_1526_);
v_c_1537_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1537_, 0, v___x_1535_);
lean_ctor_set(v_c_1537_, 1, v___x_1536_);
v___x_1538_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1525_, v_declHint_1521_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec_ref(v_env_1525_);
lean_dec(v_declHint_1521_);
v___x_1539_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v_c_1537_);
v___x_1541_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = l_Lean_MessageData_note(v___x_1542_);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_msg_1520_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
else
{
lean_object* v_val_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1581_; 
v_val_1546_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1548_ = v___x_1538_;
v_isShared_1549_ = v_isSharedCheck_1581_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_val_1546_);
lean_dec(v___x_1538_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1581_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_mod_1553_; uint8_t v___x_1554_; 
v___x_1550_ = lean_box(0);
v___x_1551_ = l_Lean_Environment_header(v_env_1525_);
lean_dec_ref(v_env_1525_);
v___x_1552_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1551_);
v_mod_1553_ = lean_array_get(v___x_1550_, v___x_1552_, v_val_1546_);
lean_dec(v_val_1546_);
lean_dec_ref(v___x_1552_);
v___x_1554_ = l_Lean_isPrivateName(v_declHint_1521_);
lean_dec(v_declHint_1521_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1555_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v_c_1537_);
v___x_1557_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_MessageData_ofName(v_mod_1553_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_MessageData_note(v___x_1562_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_msg_1520_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set_tag(v___x_1548_, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1564_);
v___x_1566_ = v___x_1548_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1568_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v_c_1537_);
v___x_1570_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l_Lean_MessageData_ofName(v_mod_1553_);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = l_Lean_MessageData_note(v___x_1575_);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v_msg_1520_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set_tag(v___x_1548_, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1577_);
v___x_1579_ = v___x_1548_;
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
}
}
}
else
{
lean_object* v___x_1582_; 
lean_dec_ref(v_env_1525_);
lean_dec(v_declHint_1521_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_msg_1520_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___boxed(lean_object* v_msg_1583_, lean_object* v_declHint_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_1583_, v_declHint_1584_, v___y_1585_);
lean_dec(v___y_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(lean_object* v_msg_1588_, lean_object* v_declHint_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1605_; 
v___x_1595_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_1588_, v_declHint_1589_, v___y_1593_);
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1600_ = l_Lean_unknownIdentifierMessageTag;
v___x_1601_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v_a_1596_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1601_);
v___x_1603_ = v___x_1598_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32___boxed(lean_object* v_msg_1606_, lean_object* v_declHint_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(v_msg_1606_, v_declHint_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(lean_object* v_ref_1614_, lean_object* v_msg_1615_, lean_object* v_declHint_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; lean_object* v_a_1623_; lean_object* v___x_1624_; 
v___x_1622_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(v_msg_1615_, v_declHint_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_1614_, v_a_1623_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg___boxed(lean_object* v_ref_1625_, lean_object* v_msg_1626_, lean_object* v_declHint_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_1625_, v_msg_1626_, v_declHint_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v_ref_1625_);
return v_res_1633_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0));
v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(lean_object* v_ref_1637_, lean_object* v_constName_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1644_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1);
v___x_1645_ = 0;
lean_inc(v_constName_1638_);
v___x_1646_ = l_Lean_MessageData_ofConstName(v_constName_1638_, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1644_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_1637_, v___x_1649_, v_constName_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___boxed(lean_object* v_ref_1651_, lean_object* v_constName_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_1651_, v_constName_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v_ref_1651_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(lean_object* v_constName_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_ref_1665_; lean_object* v___x_1666_; 
v_ref_1665_ = lean_ctor_get(v___y_1662_, 4);
v___x_1666_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_1665_, v_constName_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg___boxed(lean_object* v_constName_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object* v_constName_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; lean_object* v_env_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; 
v___x_1680_ = lean_st_ref_get(v___y_1678_);
v_env_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc_ref(v_env_1681_);
lean_dec(v___x_1680_);
v___x_1682_ = 0;
lean_inc(v_constName_1674_);
v___x_1683_ = l_Lean_Environment_find_x3f(v_env_1681_, v_constName_1674_, v___x_1682_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
return v___x_1684_;
}
else
{
lean_object* v_val_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_constName_1674_);
v_val_1685_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1683_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_val_1685_);
lean_dec(v___x_1683_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 0);
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_val_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object* v_constName_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_constName_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(lean_object* v_keys_1700_, lean_object* v_vals_1701_, lean_object* v_i_1702_, lean_object* v_k_1703_){
_start:
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = lean_array_get_size(v_keys_1700_);
v___x_1705_ = lean_nat_dec_lt(v_i_1702_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec(v_i_1702_);
v___x_1706_ = lean_box(0);
return v___x_1706_;
}
else
{
lean_object* v_k_x27_1707_; uint8_t v___x_1708_; 
v_k_x27_1707_ = lean_array_fget_borrowed(v_keys_1700_, v_i_1702_);
v___x_1708_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_k_1703_, v_k_x27_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = lean_nat_add(v_i_1702_, v___x_1709_);
lean_dec(v_i_1702_);
v_i_1702_ = v___x_1710_;
goto _start;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_array_fget_borrowed(v_vals_1701_, v_i_1702_);
lean_dec(v_i_1702_);
lean_inc(v___x_1712_);
v___x_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg___boxed(lean_object* v_keys_1714_, lean_object* v_vals_1715_, lean_object* v_i_1716_, lean_object* v_k_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_keys_1714_, v_vals_1715_, v_i_1716_, v_k_1717_);
lean_dec_ref(v_k_1717_);
lean_dec_ref(v_vals_1715_);
lean_dec_ref(v_keys_1714_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object* v_x_1719_, size_t v_x_1720_, lean_object* v_x_1721_){
_start:
{
if (lean_obj_tag(v_x_1719_) == 0)
{
lean_object* v_es_1722_; lean_object* v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; lean_object* v_j_1726_; lean_object* v___x_1727_; 
v_es_1722_ = lean_ctor_get(v_x_1719_, 0);
v___x_1723_ = lean_box(2);
v___x_1724_ = ((size_t)31ULL);
v___x_1725_ = lean_usize_land(v_x_1720_, v___x_1724_);
v_j_1726_ = lean_usize_to_nat(v___x_1725_);
v___x_1727_ = lean_array_get_borrowed(v___x_1723_, v_es_1722_, v_j_1726_);
lean_dec(v_j_1726_);
switch(lean_obj_tag(v___x_1727_))
{
case 0:
{
lean_object* v_key_1728_; lean_object* v_val_1729_; uint8_t v___x_1730_; 
v_key_1728_ = lean_ctor_get(v___x_1727_, 0);
v_val_1729_ = lean_ctor_get(v___x_1727_, 1);
v___x_1730_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_1721_, v_key_1728_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_box(0);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; 
lean_inc(v_val_1729_);
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_val_1729_);
return v___x_1732_;
}
}
case 1:
{
lean_object* v_node_1733_; size_t v___x_1734_; size_t v___x_1735_; 
v_node_1733_ = lean_ctor_get(v___x_1727_, 0);
v___x_1734_ = ((size_t)5ULL);
v___x_1735_ = lean_usize_shift_right(v_x_1720_, v___x_1734_);
v_x_1719_ = v_node_1733_;
v_x_1720_ = v___x_1735_;
goto _start;
}
default: 
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_box(0);
return v___x_1737_;
}
}
}
else
{
lean_object* v_ks_1738_; lean_object* v_vs_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_ks_1738_ = lean_ctor_get(v_x_1719_, 0);
v_vs_1739_ = lean_ctor_get(v_x_1719_, 1);
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_ks_1738_, v_vs_1739_, v___x_1740_, v_x_1721_);
return v___x_1741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_x_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_){
_start:
{
size_t v_x_22979__boxed_1745_; lean_object* v_res_1746_; 
v_x_22979__boxed_1745_ = lean_unbox_usize(v_x_1743_);
lean_dec(v_x_1743_);
v_res_1746_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_1742_, v_x_22979__boxed_1745_, v_x_1744_);
lean_dec_ref(v_x_1744_);
lean_dec_ref(v_x_1742_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
uint64_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_1748_);
v___x_1750_ = lean_uint64_to_usize(v___x_1749_);
v___x_1751_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_1747_, v___x_1750_, v_x_1748_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_1752_, v_x_1753_);
lean_dec_ref(v_x_1753_);
lean_dec_ref(v_x_1752_);
return v_res_1754_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__2(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1757_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6));
v___x_1758_ = lean_unsigned_to_nat(42u);
v___x_1759_ = lean_unsigned_to_nat(81u);
v___x_1760_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__1));
v___x_1761_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__0));
v___x_1762_ = l_mkPanicMessageWithDecl(v___x_1761_, v___x_1760_, v___x_1759_, v___x_1758_, v___x_1757_);
return v___x_1762_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__4(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__3));
v___x_1765_ = l_Lean_stringToMessageData(v___x_1764_);
return v___x_1765_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__5(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0));
v___x_1767_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0));
v___x_1768_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1767_, v___x_1766_);
return v___x_1768_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__9(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__8));
v___x_1774_ = l_Lean_stringToMessageData(v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object* v_indName_1775_, lean_object* v_ctors_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v_env_1783_; lean_object* v___x_1784_; uint8_t v_isModule_1785_; lean_object* v___x_1786_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___x_2031_; uint8_t v___y_2033_; 
v___x_1782_ = lean_st_ref_get(v_a_1780_);
v_env_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc_ref(v_env_1783_);
lean_dec(v___x_1782_);
v___x_1784_ = l_Lean_Environment_header(v_env_1783_);
v_isModule_1785_ = lean_ctor_get_uint8(v___x_1784_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1784_);
v___x_1786_ = l_Lean_instInhabitedExpr;
v___x_2031_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__5, &l_Lean_Meta_mkSparseCasesOn___closed__5_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__5);
if (v_isModule_1785_ == 0)
{
v___y_2033_ = v_isModule_1785_;
goto v___jp_2032_;
}
else
{
uint8_t v_isExporting_2090_; 
v_isExporting_2090_ = lean_ctor_get_uint8(v_env_1783_, sizeof(void*)*8);
if (v_isExporting_2090_ == 0)
{
v___y_2033_ = v_isModule_1785_;
goto v___jp_2032_;
}
else
{
uint8_t v___x_2091_; 
v___x_2091_ = 0;
v___y_2033_ = v___x_2091_;
goto v___jp_2032_;
}
}
v___jp_1787_:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_ConstantInfo_levelParams(v___y_1795_);
if (lean_obj_tag(v___x_1805_) == 1)
{
lean_object* v_tail_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___f_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; 
v_tail_1806_ = lean_ctor_get(v___x_1805_, 1);
lean_inc(v_tail_1806_);
v___x_1807_ = lean_box(0);
v___x_1808_ = l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(v_tail_1806_, v___x_1807_);
lean_inc_ref(v_ctors_1776_);
v___f_1809_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__2___boxed), 16, 9);
lean_closure_set(v___f_1809_, 0, v___y_1790_);
lean_closure_set(v___f_1809_, 1, v___x_1786_);
lean_closure_set(v___f_1809_, 2, v___y_1793_);
lean_closure_set(v___f_1809_, 3, v_ctors_1776_);
lean_closure_set(v___f_1809_, 4, v___y_1791_);
lean_closure_set(v___f_1809_, 5, v___x_1808_);
lean_closure_set(v___f_1809_, 6, v___y_1789_);
lean_closure_set(v___f_1809_, 7, v___y_1788_);
lean_closure_set(v___f_1809_, 8, v___y_1792_);
v___x_1810_ = l_Lean_ConstantInfo_type(v___y_1795_);
lean_dec_ref(v___y_1795_);
v___x_1811_ = 0;
v___x_1812_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v___x_1810_, v___f_1809_, v___x_1811_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1814_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc_n(v_a_1813_, 2);
lean_dec_ref_known(v___x_1812_, 1);
lean_inc(v___y_1804_);
lean_inc_ref(v___y_1803_);
lean_inc(v___y_1802_);
lean_inc_ref(v___y_1801_);
v___x_1814_ = lean_infer_type(v_a_1813_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1964_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1816_ = lean_box(1);
lean_inc(v___y_1800_);
v___x_1817_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___y_1800_, v___x_1805_, v_a_1815_, v_a_1813_, v___x_1816_, v___y_1804_);
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1964_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1964_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set_tag(v___x_1820_, 1);
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_addDecl(v___x_1823_, v___x_1811_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v___x_1825_; lean_object* v_env_1826_; lean_object* v_nextMacroScope_1827_; lean_object* v_ngen_1828_; lean_object* v_auxDeclNGen_1829_; lean_object* v_traceState_1830_; lean_object* v_messages_1831_; lean_object* v_infoState_1832_; lean_object* v_snapshotTasks_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref_known(v___x_1824_, 1);
v___x_1825_ = lean_st_ref_take(v___y_1804_);
v_env_1826_ = lean_ctor_get(v___x_1825_, 0);
v_nextMacroScope_1827_ = lean_ctor_get(v___x_1825_, 1);
v_ngen_1828_ = lean_ctor_get(v___x_1825_, 2);
v_auxDeclNGen_1829_ = lean_ctor_get(v___x_1825_, 3);
v_traceState_1830_ = lean_ctor_get(v___x_1825_, 4);
v_messages_1831_ = lean_ctor_get(v___x_1825_, 6);
v_infoState_1832_ = lean_ctor_get(v___x_1825_, 7);
v_snapshotTasks_1833_ = lean_ctor_get(v___x_1825_, 8);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; 
v_unused_1954_ = lean_ctor_get(v___x_1825_, 5);
lean_dec(v_unused_1954_);
v___x_1835_ = v___x_1825_;
v_isShared_1836_ = v_isSharedCheck_1953_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_snapshotTasks_1833_);
lean_inc(v_infoState_1832_);
lean_inc(v_messages_1831_);
lean_inc(v_traceState_1830_);
lean_inc(v_auxDeclNGen_1829_);
lean_inc(v_ngen_1828_);
lean_inc(v_nextMacroScope_1827_);
lean_inc(v_env_1826_);
lean_dec(v___x_1825_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1953_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
lean_inc_ref(v___y_1799_);
v___x_1837_ = l_Lean_EnvExtension_modifyState___redArg(v___y_1799_, v_env_1826_, v___y_1796_, v___y_1794_, v___y_1797_);
v___x_1838_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 5, v___x_1838_);
lean_ctor_set(v___x_1835_, 0, v___x_1837_);
v___x_1840_ = v___x_1835_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_nextMacroScope_1827_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_ngen_1828_);
lean_ctor_set(v_reuseFailAlloc_1952_, 3, v_auxDeclNGen_1829_);
lean_ctor_set(v_reuseFailAlloc_1952_, 4, v_traceState_1830_);
lean_ctor_set(v_reuseFailAlloc_1952_, 5, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1952_, 6, v_messages_1831_);
lean_ctor_set(v_reuseFailAlloc_1952_, 7, v_infoState_1832_);
lean_ctor_set(v_reuseFailAlloc_1952_, 8, v_snapshotTasks_1833_);
v___x_1840_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v_mctx_1843_; lean_object* v_zetaDeltaFVarIds_1844_; lean_object* v_postponed_1845_; lean_object* v_diag_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1950_; 
v___x_1841_ = lean_st_ref_put(v___y_1804_, v___x_1840_);
v___x_1842_ = lean_st_ref_take(v___y_1802_);
v_mctx_1843_ = lean_ctor_get(v___x_1842_, 0);
v_zetaDeltaFVarIds_1844_ = lean_ctor_get(v___x_1842_, 2);
v_postponed_1845_ = lean_ctor_get(v___x_1842_, 3);
v_diag_1846_ = lean_ctor_get(v___x_1842_, 4);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v___x_1842_, 1);
lean_dec(v_unused_1951_);
v___x_1848_ = v___x_1842_;
v_isShared_1849_ = v_isSharedCheck_1950_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_diag_1846_);
lean_inc(v_postponed_1845_);
lean_inc(v_zetaDeltaFVarIds_1844_);
lean_inc(v_mctx_1843_);
lean_dec(v___x_1842_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1950_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_mctx_1843_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_zetaDeltaFVarIds_1844_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v_postponed_1845_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v_diag_1846_);
v___x_1852_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v_env_1856_; lean_object* v_nextMacroScope_1857_; lean_object* v_ngen_1858_; lean_object* v_auxDeclNGen_1859_; lean_object* v_traceState_1860_; lean_object* v_messages_1861_; lean_object* v_infoState_1862_; lean_object* v_snapshotTasks_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1947_; 
v___x_1853_ = lean_st_ref_put(v___y_1802_, v___x_1852_);
lean_inc(v___y_1800_);
v___x_1854_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec_ref(v___x_1854_);
v___x_1855_ = lean_st_ref_take(v___y_1804_);
v_env_1856_ = lean_ctor_get(v___x_1855_, 0);
v_nextMacroScope_1857_ = lean_ctor_get(v___x_1855_, 1);
v_ngen_1858_ = lean_ctor_get(v___x_1855_, 2);
v_auxDeclNGen_1859_ = lean_ctor_get(v___x_1855_, 3);
v_traceState_1860_ = lean_ctor_get(v___x_1855_, 4);
v_messages_1861_ = lean_ctor_get(v___x_1855_, 6);
v_infoState_1862_ = lean_ctor_get(v___x_1855_, 7);
v_snapshotTasks_1863_ = lean_ctor_get(v___x_1855_, 8);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v___x_1855_, 5);
lean_dec(v_unused_1948_);
v___x_1865_ = v___x_1855_;
v_isShared_1866_ = v_isSharedCheck_1947_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_snapshotTasks_1863_);
lean_inc(v_infoState_1862_);
lean_inc(v_messages_1861_);
lean_inc(v_traceState_1860_);
lean_inc(v_auxDeclNGen_1859_);
lean_inc(v_ngen_1858_);
lean_inc(v_nextMacroScope_1857_);
lean_inc(v_env_1856_);
lean_dec(v___x_1855_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1947_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
lean_inc(v___y_1800_);
v___x_1867_ = l_Lean_markSparseCasesOn(v_env_1856_, v___y_1800_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 5, v___x_1838_);
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_nextMacroScope_1857_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_ngen_1858_);
lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_auxDeclNGen_1859_);
lean_ctor_set(v_reuseFailAlloc_1946_, 4, v_traceState_1860_);
lean_ctor_set(v_reuseFailAlloc_1946_, 5, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1946_, 6, v_messages_1861_);
lean_ctor_set(v_reuseFailAlloc_1946_, 7, v_infoState_1862_);
lean_ctor_set(v_reuseFailAlloc_1946_, 8, v_snapshotTasks_1863_);
v___x_1869_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v_mctx_1872_; lean_object* v_zetaDeltaFVarIds_1873_; lean_object* v_postponed_1874_; lean_object* v_diag_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1944_; 
v___x_1870_ = lean_st_ref_put(v___y_1804_, v___x_1869_);
v___x_1871_ = lean_st_ref_take(v___y_1802_);
v_mctx_1872_ = lean_ctor_get(v___x_1871_, 0);
v_zetaDeltaFVarIds_1873_ = lean_ctor_get(v___x_1871_, 2);
v_postponed_1874_ = lean_ctor_get(v___x_1871_, 3);
v_diag_1875_ = lean_ctor_get(v___x_1871_, 4);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v___x_1871_, 1);
lean_dec(v_unused_1945_);
v___x_1877_ = v___x_1871_;
v_isShared_1878_ = v_isSharedCheck_1944_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_diag_1875_);
lean_inc(v_postponed_1874_);
lean_inc(v_zetaDeltaFVarIds_1873_);
lean_inc(v_mctx_1872_);
lean_dec(v___x_1871_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1944_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v___x_1850_);
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_mctx_1872_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_zetaDeltaFVarIds_1873_);
lean_ctor_set(v_reuseFailAlloc_1943_, 3, v_postponed_1874_);
lean_ctor_set(v_reuseFailAlloc_1943_, 4, v_diag_1875_);
v___x_1880_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v_env_1883_; lean_object* v_nextMacroScope_1884_; lean_object* v_ngen_1885_; lean_object* v_auxDeclNGen_1886_; lean_object* v_traceState_1887_; lean_object* v_messages_1888_; lean_object* v_infoState_1889_; lean_object* v_snapshotTasks_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1941_; 
v___x_1881_ = lean_st_ref_put(v___y_1802_, v___x_1880_);
v___x_1882_ = lean_st_ref_take(v___y_1804_);
v_env_1883_ = lean_ctor_get(v___x_1882_, 0);
v_nextMacroScope_1884_ = lean_ctor_get(v___x_1882_, 1);
v_ngen_1885_ = lean_ctor_get(v___x_1882_, 2);
v_auxDeclNGen_1886_ = lean_ctor_get(v___x_1882_, 3);
v_traceState_1887_ = lean_ctor_get(v___x_1882_, 4);
v_messages_1888_ = lean_ctor_get(v___x_1882_, 6);
v_infoState_1889_ = lean_ctor_get(v___x_1882_, 7);
v_snapshotTasks_1890_ = lean_ctor_get(v___x_1882_, 8);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v___x_1882_, 5);
lean_dec(v_unused_1942_);
v___x_1892_ = v___x_1882_;
v_isShared_1893_ = v_isSharedCheck_1941_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_snapshotTasks_1890_);
lean_inc(v_infoState_1889_);
lean_inc(v_messages_1888_);
lean_inc(v_traceState_1887_);
lean_inc(v_auxDeclNGen_1886_);
lean_inc(v_ngen_1885_);
lean_inc(v_nextMacroScope_1884_);
lean_inc(v_env_1883_);
lean_dec(v___x_1882_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1941_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v_numParams_1894_; lean_object* v_numIndices_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v_numParams_1894_ = lean_ctor_get(v___y_1798_, 1);
lean_inc(v_numParams_1894_);
v_numIndices_1895_ = lean_ctor_get(v___y_1798_, 2);
lean_inc(v_numIndices_1895_);
lean_dec_ref(v___y_1798_);
v___x_1896_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = lean_nat_add(v_numParams_1894_, v___x_1897_);
lean_dec(v_numParams_1894_);
v___x_1899_ = lean_nat_add(v___x_1898_, v_numIndices_1895_);
lean_dec(v_numIndices_1895_);
lean_dec(v___x_1898_);
v___x_1900_ = lean_nat_add(v___x_1899_, v___x_1897_);
v___x_1901_ = lean_array_get_size(v_ctors_1776_);
v___x_1902_ = lean_nat_add(v___x_1900_, v___x_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_nat_add(v___x_1902_, v___x_1897_);
lean_dec(v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1904_, 0, v_indName_1775_);
lean_ctor_set(v___x_1904_, 1, v___x_1899_);
lean_ctor_set(v___x_1904_, 2, v___x_1903_);
lean_ctor_set(v___x_1904_, 3, v_ctors_1776_);
lean_inc(v___y_1800_);
v___x_1905_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1896_, v_env_1883_, v___y_1800_, v___x_1904_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 5, v___x_1838_);
lean_ctor_set(v___x_1892_, 0, v___x_1905_);
v___x_1907_ = v___x_1892_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_nextMacroScope_1884_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_ngen_1885_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_auxDeclNGen_1886_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_traceState_1887_);
lean_ctor_set(v_reuseFailAlloc_1940_, 5, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1940_, 6, v_messages_1888_);
lean_ctor_set(v_reuseFailAlloc_1940_, 7, v_infoState_1889_);
lean_ctor_set(v_reuseFailAlloc_1940_, 8, v_snapshotTasks_1890_);
v___x_1907_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v_mctx_1910_; lean_object* v_zetaDeltaFVarIds_1911_; lean_object* v_postponed_1912_; lean_object* v_diag_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1938_; 
v___x_1908_ = lean_st_ref_put(v___y_1804_, v___x_1907_);
v___x_1909_ = lean_st_ref_take(v___y_1802_);
v_mctx_1910_ = lean_ctor_get(v___x_1909_, 0);
v_zetaDeltaFVarIds_1911_ = lean_ctor_get(v___x_1909_, 2);
v_postponed_1912_ = lean_ctor_get(v___x_1909_, 3);
v_diag_1913_ = lean_ctor_get(v___x_1909_, 4);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v___x_1909_, 1);
lean_dec(v_unused_1939_);
v___x_1915_ = v___x_1909_;
v_isShared_1916_ = v_isSharedCheck_1938_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_diag_1913_);
lean_inc(v_postponed_1912_);
lean_inc(v_zetaDeltaFVarIds_1911_);
lean_inc(v_mctx_1910_);
lean_dec(v___x_1909_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1938_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___x_1850_);
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_mctx_1910_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_zetaDeltaFVarIds_1911_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v_postponed_1912_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v_diag_1913_);
v___x_1918_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_st_ref_put(v___y_1802_, v___x_1918_);
lean_inc(v___y_1800_);
v___x_1920_ = l_Lean_enableRealizationsForConst(v___y_1800_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v___x_1920_, 0);
lean_dec(v_unused_1928_);
v___x_1922_ = v___x_1920_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_dec(v___x_1920_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___y_1800_);
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___y_1800_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v___y_1800_);
v_a_1929_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1920_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1920_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
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
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_ctors_1776_);
lean_dec(v_indName_1775_);
v_a_1955_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1824_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1824_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec(v_a_1813_);
lean_dec_ref_known(v___x_1805_, 2);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_ctors_1776_);
lean_dec(v_indName_1775_);
v_a_1965_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1814_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1814_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
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
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref_known(v___x_1805_, 2);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_ctors_1776_);
lean_dec(v_indName_1775_);
v_a_1973_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1812_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1812_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_dec(v___x_1805_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v_ctors_1776_);
lean_dec(v_indName_1775_);
v___x_1981_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__2, &l_Lean_Meta_mkSparseCasesOn___closed__2_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__2);
v___x_1982_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(v___x_1981_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1982_;
}
}
v___jp_1983_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_inc(v_indName_1775_);
v___x_1997_ = l_Lean_mkCasesOnName(v_indName_1775_);
lean_inc(v___x_1997_);
v___x_1998_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(v___x_1997_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_toConstantVal_1999_; lean_object* v_a_2000_; lean_object* v_levelParams_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_toConstantVal_1999_ = lean_ctor_get(v___y_1990_, 0);
v_a_2000_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1998_, 1);
v_levelParams_2001_ = lean_ctor_get(v_toConstantVal_1999_, 1);
lean_inc(v_indName_1775_);
v___x_2002_ = l_Lean_mkCtorIdxName(v_indName_1775_);
v___x_2003_ = l_Lean_ConstantInfo_levelParams(v_a_2000_);
v___x_2004_ = l_List_lengthTR___redArg(v___x_2003_);
lean_dec(v___x_2003_);
v___x_2005_ = l_List_lengthTR___redArg(v_levelParams_2001_);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_add(v___x_2005_, v___x_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_nat_dec_eq(v___x_2004_, v___x_2007_);
lean_dec(v___x_2007_);
lean_dec(v___x_2004_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v___x_2002_);
lean_dec(v_a_2000_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v_ctors_1776_);
lean_dec(v_indName_1775_);
v___x_2009_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__4, &l_Lean_Meta_mkSparseCasesOn___closed__4_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__4);
v___x_2010_ = l_Lean_MessageData_ofConstName(v___x_1997_, v___x_2008_);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_2013_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
else
{
lean_inc(v_a_2000_);
v___y_1788_ = v___y_1984_;
v___y_1789_ = v_a_2000_;
v___y_1790_ = v___y_1985_;
v___y_1791_ = v___x_2002_;
v___y_1792_ = v___x_1997_;
v___y_1793_ = v___y_1987_;
v___y_1794_ = v___y_1988_;
v___y_1795_ = v_a_2000_;
v___y_1796_ = v___y_1986_;
v___y_1797_ = v___y_1989_;
v___y_1798_ = v___y_1990_;
v___y_1799_ = v___y_1991_;
v___y_1800_ = v___y_1992_;
v___y_1801_ = v___y_1993_;
v___y_1802_ = v___y_1994_;
v___y_1803_ = v___y_1995_;
v___y_1804_ = v___y_1996_;
goto v___jp_1787_;
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v___x_1997_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v_ctors_1776_);
lean_dec(v_indName_1775_);
v_a_2023_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1998_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1998_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
v___jp_2032_:
{
lean_object* v___x_2034_; lean_object* v_asyncMode_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2034_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
v_asyncMode_2035_ = lean_ctor_get(v___x_2034_, 2);
lean_inc_ref(v_ctors_1776_);
lean_inc(v_indName_1775_);
v___x_2036_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2036_, 0, v_indName_1775_);
lean_ctor_set(v___x_2036_, 1, v_ctors_1776_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*2, v___y_2033_);
v___x_2037_ = lean_box(0);
v___x_2038_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2031_, v___x_2034_, v_env_1783_, v_asyncMode_2035_, v___x_2037_);
v___x_2039_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v___x_2038_, v___x_2036_);
lean_dec(v___x_2038_);
if (lean_obj_tag(v___x_2039_) == 1)
{
lean_object* v_val_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref_known(v___x_2036_, 2);
lean_dec_ref(v_ctors_1776_);
lean_dec(v_indName_1775_);
v_val_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_val_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 0);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_val_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v_a_2050_; lean_object* v___x_2051_; 
lean_dec(v___x_2039_);
v___x_2048_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__7));
v___x_2049_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v___x_2048_, v_a_1780_);
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
lean_inc(v_indName_1775_);
v___x_2051_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(v_indName_1775_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; size_t v_sz_2054_; size_t v___x_2055_; lean_object* v___x_2056_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = lean_box(0);
v_sz_2054_ = lean_array_size(v_ctors_1776_);
v___x_2055_ = ((size_t)0ULL);
lean_inc(v_indName_1775_);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_2052_, v_indName_1775_, v_ctors_1776_, v_sz_2054_, v___x_2055_, v___x_2053_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_numParams_2057_; lean_object* v_numIndices_2058_; lean_object* v_ctors_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
lean_dec_ref_known(v___x_2056_, 1);
v_numParams_2057_ = lean_ctor_get(v_a_2052_, 1);
lean_inc(v_numParams_2057_);
v_numIndices_2058_ = lean_ctor_get(v_a_2052_, 2);
lean_inc(v_numIndices_2058_);
v_ctors_2059_ = lean_ctor_get(v_a_2052_, 4);
lean_inc(v_ctors_2059_);
lean_inc(v_a_2050_);
v___f_2060_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__0), 3, 2);
lean_closure_set(v___f_2060_, 0, v___x_2036_);
lean_closure_set(v___f_2060_, 1, v_a_2050_);
v___x_2061_ = lean_array_get_size(v_ctors_1776_);
v___x_2062_ = l_List_lengthTR___redArg(v_ctors_2059_);
v___x_2063_ = lean_nat_dec_eq(v___x_2061_, v___x_2062_);
lean_dec(v___x_2062_);
if (v___x_2063_ == 0)
{
v___y_1984_ = v_ctors_2059_;
v___y_1985_ = v_numParams_2057_;
v___y_1986_ = v___f_2060_;
v___y_1987_ = v_numIndices_2058_;
v___y_1988_ = v_asyncMode_2035_;
v___y_1989_ = v___x_2037_;
v___y_1990_ = v_a_2052_;
v___y_1991_ = v___x_2034_;
v___y_1992_ = v_a_2050_;
v___y_1993_ = v_a_1777_;
v___y_1994_ = v_a_1778_;
v___y_1995_ = v_a_1779_;
v___y_1996_ = v_a_1780_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v___f_2060_);
lean_dec(v_ctors_2059_);
lean_dec(v_numIndices_2058_);
lean_dec(v_numParams_2057_);
lean_dec(v_a_2052_);
lean_dec(v_a_2050_);
lean_dec_ref(v_ctors_1776_);
lean_dec(v_indName_1775_);
v___x_2064_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__9, &l_Lean_Meta_mkSparseCasesOn___closed__9_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__9);
v___x_2065_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_2064_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_a_2052_);
lean_dec(v_a_2050_);
lean_dec_ref_known(v___x_2036_, 2);
lean_dec_ref(v_ctors_1776_);
lean_dec(v_indName_1775_);
v_a_2074_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2056_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2056_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_a_2050_);
lean_dec_ref_known(v___x_2036_, 2);
lean_dec_ref(v_ctors_1776_);
lean_dec(v_indName_1775_);
v_a_2082_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2051_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2051_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object* v_indName_2092_, lean_object* v_ctors_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Meta_mkSparseCasesOn(v_indName_2092_, v_ctors_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object* v_00_u03b2_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_2101_, v_x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object* v_00_u03b2_2104_, lean_object* v_x_2105_, lean_object* v_x_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(v_00_u03b2_2104_, v_x_2105_, v_x_2106_);
lean_dec_ref(v_x_2106_);
lean_dec_ref(v_x_2105_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object* v_00_u03b2_2108_, lean_object* v_x_2109_, lean_object* v_x_2110_, lean_object* v_x_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_x_2109_, v_x_2110_, v_x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(lean_object* v_00_u03b1_2113_, lean_object* v_name_2114_, uint8_t v_bi_2115_, lean_object* v_type_2116_, lean_object* v_k_2117_, uint8_t v_kind_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_2114_, v_bi_2115_, v_type_2116_, v_k_2117_, v_kind_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___boxed(lean_object* v_00_u03b1_2125_, lean_object* v_name_2126_, lean_object* v_bi_2127_, lean_object* v_type_2128_, lean_object* v_k_2129_, lean_object* v_kind_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
uint8_t v_bi_boxed_2136_; uint8_t v_kind_boxed_2137_; lean_object* v_res_2138_; 
v_bi_boxed_2136_ = lean_unbox(v_bi_2127_);
v_kind_boxed_2137_ = lean_unbox(v_kind_2130_);
v_res_2138_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(v_00_u03b1_2125_, v_name_2126_, v_bi_boxed_2136_, v_type_2128_, v_k_2129_, v_kind_boxed_2137_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(lean_object* v_00_u03b1_2139_, lean_object* v_name_2140_, lean_object* v_type_2141_, lean_object* v_k_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v_name_2140_, v_type_2141_, v_k_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object* v_00_u03b1_2149_, lean_object* v_name_2150_, lean_object* v_type_2151_, lean_object* v_k_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_00_u03b1_2149_, v_name_2150_, v_type_2151_, v_k_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object* v_00_u03b1_2159_, lean_object* v_msg_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v_msg_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object* v_00_u03b1_2167_, lean_object* v_msg_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_00_u03b1_2167_, v_msg_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(lean_object* v_declName_2175_, uint8_t v_s_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_2175_, v_s_2176_, v___y_2178_, v___y_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___boxed(lean_object* v_declName_2183_, lean_object* v_s_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v_s_boxed_2190_; lean_object* v_res_2191_; 
v_s_boxed_2190_ = lean_unbox(v_s_2184_);
v_res_2191_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(v_declName_2183_, v_s_boxed_2190_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object* v_00_u03b2_2192_, lean_object* v_x_2193_, size_t v_x_2194_, lean_object* v_x_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_2193_, v_x_2194_, v_x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
size_t v_x_23747__boxed_2201_; lean_object* v_res_2202_; 
v_x_23747__boxed_2201_ = lean_unbox_usize(v_x_2199_);
lean_dec(v_x_2199_);
v_res_2202_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(v_00_u03b2_2197_, v_x_2198_, v_x_23747__boxed_2201_, v_x_2200_);
lean_dec_ref(v_x_2200_);
lean_dec_ref(v_x_2198_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object* v_00_u03b2_2203_, lean_object* v_x_2204_, size_t v_x_2205_, size_t v_x_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_2204_, v_x_2205_, v_x_2206_, v_x_2207_, v_x_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2210_, lean_object* v_x_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_){
_start:
{
size_t v_x_23758__boxed_2216_; size_t v_x_23759__boxed_2217_; lean_object* v_res_2218_; 
v_x_23758__boxed_2216_ = lean_unbox_usize(v_x_2212_);
lean_dec(v_x_2212_);
v_x_23759__boxed_2217_ = lean_unbox_usize(v_x_2213_);
lean_dec(v_x_2213_);
v_res_2218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(v_00_u03b2_2210_, v_x_2211_, v_x_23758__boxed_2216_, v_x_23759__boxed_2217_, v_x_2214_, v_x_2215_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(lean_object* v_00_u03b1_2219_, lean_object* v_constName_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_constName_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(v_00_u03b1_2227_, v_constName_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2235_, lean_object* v_keys_2236_, lean_object* v_vals_2237_, lean_object* v_heq_2238_, lean_object* v_i_2239_, lean_object* v_k_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_keys_2236_, v_vals_2237_, v_i_2239_, v_k_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___boxed(lean_object* v_00_u03b2_2242_, lean_object* v_keys_2243_, lean_object* v_vals_2244_, lean_object* v_heq_2245_, lean_object* v_i_2246_, lean_object* v_k_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(v_00_u03b2_2242_, v_keys_2243_, v_vals_2244_, v_heq_2245_, v_i_2246_, v_k_2247_);
lean_dec_ref(v_k_2247_);
lean_dec_ref(v_vals_2244_);
lean_dec_ref(v_keys_2243_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2249_, lean_object* v_n_2250_, lean_object* v_k_2251_, lean_object* v_v_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(v_n_2250_, v_k_2251_, v_v_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2254_, size_t v_depth_2255_, lean_object* v_keys_2256_, lean_object* v_vals_2257_, lean_object* v_heq_2258_, lean_object* v_i_2259_, lean_object* v_entries_2260_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_depth_2255_, v_keys_2256_, v_vals_2257_, v_i_2259_, v_entries_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___boxed(lean_object* v_00_u03b2_2262_, lean_object* v_depth_2263_, lean_object* v_keys_2264_, lean_object* v_vals_2265_, lean_object* v_heq_2266_, lean_object* v_i_2267_, lean_object* v_entries_2268_){
_start:
{
size_t v_depth_boxed_2269_; lean_object* v_res_2270_; 
v_depth_boxed_2269_ = lean_unbox_usize(v_depth_2263_);
lean_dec(v_depth_2263_);
v_res_2270_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(v_00_u03b2_2262_, v_depth_boxed_2269_, v_keys_2264_, v_vals_2265_, v_heq_2266_, v_i_2267_, v_entries_2268_);
lean_dec_ref(v_vals_2265_);
lean_dec_ref(v_keys_2264_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(lean_object* v_00_u03b1_2271_, lean_object* v_ref_2272_, lean_object* v_constName_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_2272_, v_constName_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___boxed(lean_object* v_00_u03b1_2280_, lean_object* v_ref_2281_, lean_object* v_constName_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(v_00_u03b1_2280_, v_ref_2281_, v_constName_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v_ref_2281_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26(lean_object* v_00_u03b2_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_, lean_object* v_x_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(v_x_2290_, v_x_2291_, v_x_2292_, v_x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(lean_object* v_00_u03b1_2295_, lean_object* v_ref_2296_, lean_object* v_msg_2297_, lean_object* v_declHint_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_2296_, v_msg_2297_, v_declHint_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___boxed(lean_object* v_00_u03b1_2305_, lean_object* v_ref_2306_, lean_object* v_msg_2307_, lean_object* v_declHint_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(v_00_u03b1_2305_, v_ref_2306_, v_msg_2307_, v_declHint_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v_ref_2306_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(lean_object* v_msg_2315_, lean_object* v_declHint_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_2315_, v_declHint_2316_, v___y_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___boxed(lean_object* v_msg_2323_, lean_object* v_declHint_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(v_msg_2323_, v_declHint_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(lean_object* v_00_u03b1_2331_, lean_object* v_ref_2332_, lean_object* v_msg_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_2332_, v_msg_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___boxed(lean_object* v_00_u03b1_2340_, lean_object* v_ref_2341_, lean_object* v_msg_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(v_00_u03b1_2340_, v_ref_2341_, v_msg_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v_ref_2341_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object* v_env_2349_, lean_object* v_sparseCasesOnName_2350_){
_start:
{
lean_object* v___x_2351_; lean_object* v_toEnvExtension_2352_; lean_object* v_asyncMode_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2351_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2352_ = lean_ctor_get(v___x_2351_, 0);
v_asyncMode_2353_ = lean_ctor_get(v_toEnvExtension_2352_, 2);
v___x_2354_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2355_ = 0;
v___x_2356_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2354_, v___x_2351_, v_env_2349_, v_sparseCasesOnName_2350_, v_asyncMode_2353_, v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object* v_sparseCasesOnName_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v_env_2361_; lean_object* v___x_2362_; lean_object* v_toEnvExtension_2363_; lean_object* v_asyncMode_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2360_ = lean_st_ref_get(v_a_2358_);
v_env_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc_ref(v_env_2361_);
lean_dec(v___x_2360_);
v___x_2362_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2363_ = lean_ctor_get(v___x_2362_, 0);
v_asyncMode_2364_ = lean_ctor_get(v_toEnvExtension_2363_, 2);
v___x_2365_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2366_ = 0;
v___x_2367_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2365_, v___x_2362_, v_env_2361_, v_sparseCasesOnName_2357_, v_asyncMode_2364_, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object* v_sparseCasesOnName_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2369_, v_a_2370_);
lean_dec(v_a_2370_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object* v_sparseCasesOnName_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2373_, v_a_2375_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object* v_sparseCasesOnName_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Meta_getSparseCasesOnInfo(v_sparseCasesOnName_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v_res_2382_;
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
