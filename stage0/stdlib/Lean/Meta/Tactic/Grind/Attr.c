// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Attr
// Imports: public import Lean.Meta.Tactic.Grind.Injective public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.ExtAttr public import Lean.Meta.Tactic.Simp.Attr public import Lean.Meta.Tactic.Grind.Homo public import Lean.Meta.Sym.DSimp.Rewrite import Lean.Meta.Sym.Simp.Attr import Lean.ExtraModUses
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_mkExtension(lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_addDeclToUnfold(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_addEntry(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_mkEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateExtAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSymbolPriorityAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpTheoremFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default;
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "normExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 117, 24, 11, 244, 218, 170, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normExt;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "norm"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 82, 242, 154, 5, 26, 236, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 98, 249, 2, 230, 183, 10, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 254, 122, 13, 209, 4, 96, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 171, 221, 227, 25, 133, 195, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 72, 241, 93, 31, 88, 24, 156)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 99, 64, 101, 196, 242, 78, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 102, 233, 244, 63, 110, 171, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 38, 22, 238, 56, 195, 101, 225)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 32, 197, 231, 9, 105, 134, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 8, 248, 216, 120, 97, 211, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 115, 203, 254, 31, 135, 121, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 182, 250, 113, 105, 31, 65, 165)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 202, 156, 167, 66, 153, 39, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 187, 236, 120, 172, 89, 32, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(448808965) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(24, 160, 99, 55, 202, 33, 244, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 159, 216, 39, 51, 61, 141, 72)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 73, 198, 215, 12, 41, 81, 204)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(146, 108, 201, 9, 220, 24, 56, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymEntry_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymEntry;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymTheorems_addEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_NormSymEntry_declName_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "normSymExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 33, 18, 12, 138, 185, 216, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_NormSymTheorems_addEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSymExt;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "skipping `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`, not a global declaration"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "skipping unfold `"};
static const lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "unexpected `grind` theorem kind: `"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__4;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__6;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindEq"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindDef"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value),LEAN_SCALAR_PTR_LITERAL(66, 218, 12, 28, 39, 29, 4, 77)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindFwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value),LEAN_SCALAR_PTR_LITERAL(121, 161, 177, 116, 112, 162, 92, 47)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value),LEAN_SCALAR_PTR_LITERAL(114, 163, 57, 243, 160, 41, 114, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqRhs"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value),LEAN_SCALAR_PTR_LITERAL(222, 187, 148, 221, 105, 213, 199, 68)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindEqBoth"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value),LEAN_SCALAR_PTR_LITERAL(79, 230, 133, 190, 186, 228, 109, 128)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value),LEAN_SCALAR_PTR_LITERAL(250, 57, 23, 180, 238, 116, 90, 53)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindLR"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value),LEAN_SCALAR_PTR_LITERAL(152, 111, 188, 78, 132, 212, 97, 164)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindRL"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value),LEAN_SCALAR_PTR_LITERAL(84, 112, 237, 169, 105, 148, 42, 205)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindUsr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value),LEAN_SCALAR_PTR_LITERAL(204, 58, 160, 148, 192, 167, 114, 18)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindGen"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value),LEAN_SCALAR_PTR_LITERAL(186, 203, 120, 147, 97, 215, 208, 134)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindCases"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value),LEAN_SCALAR_PTR_LITERAL(85, 142, 28, 230, 49, 50, 229, 162)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grindCasesEager"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value),LEAN_SCALAR_PTR_LITERAL(75, 210, 92, 40, 190, 183, 142, 70)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindIntro"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value),LEAN_SCALAR_PTR_LITERAL(142, 126, 114, 89, 237, 253, 56, 138)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindExt"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value),LEAN_SCALAR_PTR_LITERAL(147, 193, 153, 166, 243, 149, 163, 253)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindInj"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 41, 9, 21, 5, 145, 193)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindFunCC"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value),LEAN_SCALAR_PTR_LITERAL(217, 20, 186, 134, 249, 79, 78, 43)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value),LEAN_SCALAR_PTR_LITERAL(166, 126, 146, 239, 104, 253, 29, 148)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindUnfold"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value),LEAN_SCALAR_PTR_LITERAL(214, 181, 37, 92, 122, 232, 164, 219)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindHom"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value),LEAN_SCALAR_PTR_LITERAL(14, 226, 234, 13, 148, 139, 225, 180)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grindHomFallback"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value),LEAN_SCALAR_PTR_LITERAL(140, 210, 151, 50, 71, 98, 251, 189)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindHomPred"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value),LEAN_SCALAR_PTR_LITERAL(1, 153, 163, 64, 153, 27, 218, 140)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__58 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__61 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__62 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__63 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__64 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__65 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__65_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "the modifier `usr` is only relevant in parameters for `grind only`"};
static const lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "cannot mark declaration to be unfolded by `grind`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "invalid `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " intro]`, `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "symbol priorities must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "normalizer must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "declaration to unfold must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "homomorphism rules must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "homomorphism predicates must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "When applied to an equational theorem, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " =]`, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " =_]`, or `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = " _=_]`will mark the theorem for use in heuristic instantiations by the `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 135, .m_data = "` tactic,\n      using respectively the left-hand side, the right-hand side, or both sides of the theorem.When applied to a function, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = " =]` automatically annotates the equational theorems associated with that function.When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 183, .m_capacity = 183, .m_length = 180, .m_data = " ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem\n      (that is, it will use the theorem for backwards reasoning).When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 190, .m_capacity = 190, .m_length = 187, .m_data = " →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses\n      (that is, it will use the theorem for forwards reasoning).The attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "]` by itself will effectively try `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 68, .m_data = " ←]` (if the conclusion is sufficient for instantiation) and then `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 162, .m_data = " →]`.The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.For example, if a theorem `@["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 179, .m_capacity = 179, .m_length = 178, .m_data = " =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,`grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "The `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "]` attribute is used to annotate declarations."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "!]` attribute is used to annotate declarations, but selecting minimal indexable subterms."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "!\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "!]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_extensionMapRef;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value),LEAN_SCALAR_PTR_LITERAL(160, 1, 171, 211, 177, 132, 129, 49)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_grindExt;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 161, 226, 116, 111, 153, 146, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "liaExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 224, 62, 90, 13, 174, 224, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liaExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_mkSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_94_ = 0;
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_96_ = l_Lean_registerTraceClass(v___x_93_, v___x_94_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2____boxed(lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_();
return v_res_98_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = l_Lean_NameSet_empty;
v___x_105_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3);
v___x_108_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2);
v___x_109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
lean_ctor_set(v___x_109_, 2, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default;
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl(lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_tag_nat(v_x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl___boxed(lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl(v_x_114_);
lean_dec_ref(v_x_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(lean_object* v_t_116_, lean_object* v_k_117_){
_start:
{
lean_object* v_thm_118_; lean_object* v___x_119_; 
v_thm_118_ = lean_ctor_get(v_t_116_, 0);
lean_inc_ref(v_thm_118_);
lean_dec_ref(v_t_116_);
v___x_119_ = lean_apply_1(v_k_117_, v_thm_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim(lean_object* v_motive_120_, lean_object* v_ctorIdx_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_k_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_122_, v_k_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___boxed(lean_object* v_motive_126_, lean_object* v_ctorIdx_127_, lean_object* v_t_128_, lean_object* v_h_129_, lean_object* v_k_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim(v_motive_126_, v_ctorIdx_127_, v_t_128_, v_h_129_, v_k_130_);
lean_dec(v_ctorIdx_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim___redArg(lean_object* v_t_132_, lean_object* v_pre_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_132_, v_pre_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim(lean_object* v_motive_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_pre_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_136_, v_pre_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim___redArg(lean_object* v_t_140_, lean_object* v_post_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_140_, v_post_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim(lean_object* v_motive_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_post_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_144_, v_post_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim___redArg(lean_object* v_t_148_, lean_object* v_dsimp_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_148_, v_dsimp_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim(lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_dsimp_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_152_, v_dsimp_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default;
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_Grind_instInhabitedNormSymEntry_default;
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymTheorems_addEntry(lean_object* v_s_160_, lean_object* v_x_161_){
_start:
{
switch(lean_obj_tag(v_x_161_))
{
case 0:
{
lean_object* v_thm_162_; lean_object* v_pre_163_; lean_object* v_post_164_; lean_object* v_dsimp_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
v_thm_162_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_thm_162_);
lean_dec_ref_known(v_x_161_, 1);
v_pre_163_ = lean_ctor_get(v_s_160_, 0);
v_post_164_ = lean_ctor_get(v_s_160_, 1);
v_dsimp_165_ = lean_ctor_get(v_s_160_, 2);
v_isSharedCheck_173_ = !lean_is_exclusive(v_s_160_);
if (v_isSharedCheck_173_ == 0)
{
v___x_167_ = v_s_160_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_dsimp_165_);
lean_inc(v_post_164_);
lean_inc(v_pre_163_);
lean_dec(v_s_160_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_pre_163_, v_thm_162_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_post_164_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_dsimp_165_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
case 1:
{
lean_object* v_thm_174_; lean_object* v_pre_175_; lean_object* v_post_176_; lean_object* v_dsimp_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_185_; 
v_thm_174_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_thm_174_);
lean_dec_ref_known(v_x_161_, 1);
v_pre_175_ = lean_ctor_get(v_s_160_, 0);
v_post_176_ = lean_ctor_get(v_s_160_, 1);
v_dsimp_177_ = lean_ctor_get(v_s_160_, 2);
v_isSharedCheck_185_ = !lean_is_exclusive(v_s_160_);
if (v_isSharedCheck_185_ == 0)
{
v___x_179_ = v_s_160_;
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_dsimp_177_);
lean_inc(v_post_176_);
lean_inc(v_pre_175_);
lean_dec(v_s_160_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_post_176_, v_thm_174_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_181_);
v___x_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_pre_175_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_dsimp_177_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
default: 
{
lean_object* v_entry_186_; lean_object* v_pre_187_; lean_object* v_post_188_; lean_object* v_dsimp_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_197_; 
v_entry_186_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_entry_186_);
lean_dec_ref_known(v_x_161_, 1);
v_pre_187_ = lean_ctor_get(v_s_160_, 0);
v_post_188_ = lean_ctor_get(v_s_160_, 1);
v_dsimp_189_ = lean_ctor_get(v_s_160_, 2);
v_isSharedCheck_197_ = !lean_is_exclusive(v_s_160_);
if (v_isSharedCheck_197_ == 0)
{
v___x_191_ = v_s_160_;
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_dsimp_189_);
lean_inc(v_post_188_);
lean_inc(v_pre_187_);
lean_dec(v_s_160_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_Meta_Sym_DSimp_Decls_addEntry(v_dsimp_189_, v_entry_186_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 2, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_pre_187_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_post_188_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_NormSymEntry_declName_x3f(lean_object* v_x_198_){
_start:
{
lean_object* v_thm_200_; 
if (lean_obj_tag(v_x_198_) == 2)
{
lean_object* v_entry_205_; 
v_entry_205_ = lean_ctor_get(v_x_198_, 0);
lean_inc_ref(v_entry_205_);
lean_dec_ref_known(v_x_198_, 1);
if (lean_obj_tag(v_entry_205_) == 0)
{
lean_object* v_thm_206_; 
v_thm_206_ = lean_ctor_get(v_entry_205_, 0);
lean_inc_ref(v_thm_206_);
lean_dec_ref_known(v_entry_205_, 1);
v_thm_200_ = v_thm_206_;
goto v___jp_199_;
}
else
{
lean_object* v_declName_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_declName_207_ = lean_ctor_get(v_entry_205_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_entry_205_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v_entry_205_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_declName_207_);
lean_dec(v_entry_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_declName_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v_thm_215_; 
v_thm_215_ = lean_ctor_get(v_x_198_, 0);
lean_inc_ref(v_thm_215_);
lean_dec_ref(v_x_198_);
v_thm_200_ = v_thm_215_;
goto v___jp_199_;
}
v___jp_199_:
{
lean_object* v_expr_201_; 
v_expr_201_ = lean_ctor_get(v_thm_200_, 0);
lean_inc_ref(v_expr_201_);
lean_dec_ref(v_thm_200_);
if (lean_obj_tag(v_expr_201_) == 4)
{
lean_object* v_declName_202_; lean_object* v___x_203_; 
v_declName_202_ = lean_ctor_get(v_expr_201_, 0);
lean_inc(v_declName_202_);
lean_dec_ref_known(v_expr_201_, 2);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v_declName_202_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; 
lean_dec_ref(v_expr_201_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object* v_x_216_, lean_object* v_e_217_){
_start:
{
lean_object* v___x_218_; 
lean_inc_ref(v_e_217_);
v___x_218_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_NormSymEntry_declName_x3f(v_e_217_);
if (lean_obj_tag(v___x_218_) == 1)
{
lean_object* v_val_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_233_; 
v_val_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_233_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_233_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_val_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_233_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; 
v___x_223_ = l_Lean_isPrivateName(v_val_219_);
lean_dec(v_val_219_);
if (v___x_223_ == 0)
{
lean_object* v___x_225_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_e_217_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_e_217_);
v___x_225_ = v_reuseFailAlloc_227_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
lean_inc_ref_n(v___x_225_, 2);
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
lean_ctor_set(v___x_226_, 2, v___x_225_);
return v___x_226_;
}
}
else
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_box(0);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_e_217_);
v___x_230_ = v___x_221_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_e_217_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_228_);
lean_ctor_set(v___x_231_, 1, v___x_228_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
return v___x_231_;
}
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v___x_218_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v_e_217_);
lean_inc_ref_n(v___x_234_, 2);
v___x_235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v_x_236_, lean_object* v_e_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(v_x_236_, v_e_237_);
lean_dec_ref(v_x_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object* v___y_239_){
_start:
{
lean_inc_ref(v___y_239_);
return v___y_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(v___y_240_);
lean_dec_ref(v___y_240_);
return v_res_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_251_ = lean_box(0);
v___x_252_ = 0;
v___f_253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___f_254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_255_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4);
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_258_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
lean_ctor_set(v___x_258_, 2, v___x_255_);
lean_ctor_set(v___x_258_, 3, v___f_254_);
lean_ctor_set(v___x_258_, 4, v___f_253_);
lean_ctor_set(v___x_258_, 5, v___x_251_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*6, v___x_252_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*6 + 1, v___x_252_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_);
v___x_261_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_();
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(lean_object* v_____r_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0));
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___boxed(lean_object* v_____r_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v_____r_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_env_288_; uint8_t v___x_289_; lean_object* v_env_290_; lean_object* v___x_291_; lean_object* v_toCold_292_; lean_object* v_mctx_293_; lean_object* v_lctx_294_; lean_object* v_options_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_287_ = lean_st_ref_get(v___y_285_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc_ref(v_env_288_);
lean_dec(v___x_287_);
v___x_289_ = 0;
v_env_290_ = l_Lean_Environment_setRecordingDeps(v_env_288_, v___x_289_);
v___x_291_ = lean_st_ref_get(v___y_283_);
v_toCold_292_ = lean_ctor_get(v___y_284_, 0);
v_mctx_293_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_mctx_293_);
lean_dec(v___x_291_);
v_lctx_294_ = lean_ctor_get(v___y_282_, 2);
v_options_295_ = lean_ctor_get(v_toCold_292_, 2);
lean_inc_ref(v_options_295_);
lean_inc_ref(v_lctx_294_);
v___x_296_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_296_, 0, v_env_290_);
lean_ctor_set(v___x_296_, 1, v_mctx_293_);
lean_ctor_set(v___x_296_, 2, v_lctx_294_);
lean_ctor_set(v___x_296_, 3, v_options_295_);
v___x_297_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_msgData_281_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msgData_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_305_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_306_; double v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_float_of_nat(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(lean_object* v_cls_311_, lean_object* v_msg_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_ref_318_; lean_object* v___x_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_365_; 
v_ref_318_ = lean_ctor_get(v___y_315_, 2);
v___x_319_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msg_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_365_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_365_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_365_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v_traceState_325_; lean_object* v_env_326_; lean_object* v_nextMacroScope_327_; lean_object* v_ngen_328_; lean_object* v_auxDeclNGen_329_; lean_object* v_cache_330_; lean_object* v_recordedDeps_331_; lean_object* v_messages_332_; lean_object* v_infoState_333_; lean_object* v_snapshotTasks_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_364_; 
v___x_324_ = lean_st_ref_take(v___y_316_);
v_traceState_325_ = lean_ctor_get(v___x_324_, 4);
v_env_326_ = lean_ctor_get(v___x_324_, 0);
v_nextMacroScope_327_ = lean_ctor_get(v___x_324_, 1);
v_ngen_328_ = lean_ctor_get(v___x_324_, 2);
v_auxDeclNGen_329_ = lean_ctor_get(v___x_324_, 3);
v_cache_330_ = lean_ctor_get(v___x_324_, 5);
v_recordedDeps_331_ = lean_ctor_get(v___x_324_, 6);
v_messages_332_ = lean_ctor_get(v___x_324_, 7);
v_infoState_333_ = lean_ctor_get(v___x_324_, 8);
v_snapshotTasks_334_ = lean_ctor_get(v___x_324_, 9);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_364_ == 0)
{
v___x_336_ = v___x_324_;
v_isShared_337_ = v_isSharedCheck_364_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snapshotTasks_334_);
lean_inc(v_infoState_333_);
lean_inc(v_messages_332_);
lean_inc(v_recordedDeps_331_);
lean_inc(v_cache_330_);
lean_inc(v_traceState_325_);
lean_inc(v_auxDeclNGen_329_);
lean_inc(v_ngen_328_);
lean_inc(v_nextMacroScope_327_);
lean_inc(v_env_326_);
lean_dec(v___x_324_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_364_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
uint64_t v_tid_338_; lean_object* v_traces_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_363_; 
v_tid_338_ = lean_ctor_get_uint64(v_traceState_325_, sizeof(void*)*1);
v_traces_339_ = lean_ctor_get(v_traceState_325_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_traceState_325_);
if (v_isSharedCheck_363_ == 0)
{
v___x_341_ = v_traceState_325_;
v_isShared_342_ = v_isSharedCheck_363_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_traces_339_);
lean_dec(v_traceState_325_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_363_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_344_; double v___x_345_; uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_343_ = lean_box(0);
v___x_344_ = lean_box(0);
v___x_345_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0);
v___x_346_ = 0;
v___x_347_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_348_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_348_, 0, v_cls_311_);
lean_ctor_set(v___x_348_, 1, v___x_344_);
lean_ctor_set(v___x_348_, 2, v___x_347_);
lean_ctor_set_float(v___x_348_, sizeof(void*)*3, v___x_345_);
lean_ctor_set_float(v___x_348_, sizeof(void*)*3 + 8, v___x_345_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*3 + 16, v___x_346_);
v___x_349_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2));
v___x_350_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v_a_320_);
lean_ctor_set(v___x_350_, 2, v___x_349_);
lean_inc(v_ref_318_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_ref_318_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = l_Lean_PersistentArray_push___redArg(v_traces_339_, v___x_351_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_352_);
v___x_354_ = v___x_341_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_352_);
lean_ctor_set_uint64(v_reuseFailAlloc_362_, sizeof(void*)*1, v_tid_338_);
v___x_354_ = v_reuseFailAlloc_362_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 4, v___x_354_);
v___x_356_ = v___x_336_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_env_326_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_nextMacroScope_327_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_ngen_328_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_auxDeclNGen_329_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_361_, 5, v_cache_330_);
lean_ctor_set(v_reuseFailAlloc_361_, 6, v_recordedDeps_331_);
lean_ctor_set(v_reuseFailAlloc_361_, 7, v_messages_332_);
lean_ctor_set(v_reuseFailAlloc_361_, 8, v_infoState_333_);
lean_ctor_set(v_reuseFailAlloc_361_, 9, v_snapshotTasks_334_);
v___x_356_ = v_reuseFailAlloc_361_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = lean_st_ref_put(v___y_316_, v___x_356_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_343_);
v___x_359_ = v___x_322_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_343_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___boxed(lean_object* v_cls_366_, lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_366_, v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1));
v___x_379_ = l_Lean_Name_append(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(lean_object* v_thm_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___y_396_; lean_object* v_proof_409_; 
v_proof_409_ = lean_ctor_get(v_thm_389_, 2);
if (lean_obj_tag(v_proof_409_) == 4)
{
lean_object* v_declName_410_; lean_object* v___x_414_; 
lean_inc_ref(v_proof_409_);
lean_dec_ref(v_thm_389_);
v_declName_410_ = lean_ctor_get(v_proof_409_, 0);
lean_inc_n(v_declName_410_, 2);
lean_dec_ref_known(v_proof_409_, 2);
v___x_414_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_410_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_declName_410_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_423_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_a_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_461_; 
v_a_424_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_461_ == 0)
{
v___x_426_ = v___x_414_;
v_isShared_427_ = v_isSharedCheck_461_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_414_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_461_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___x_428_; 
v___x_428_ = l_Lean_Exception_isInterrupt(v_a_424_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
lean_inc(v_a_424_);
v___x_429_ = l_Lean_Exception_isRuntime(v_a_424_);
if (v___x_429_ == 0)
{
lean_object* v_toCold_430_; lean_object* v_options_431_; uint8_t v_hasTrace_432_; 
lean_del_object(v___x_426_);
v_toCold_430_ = lean_ctor_get(v_a_392_, 0);
v_options_431_ = lean_ctor_get(v_toCold_430_, 2);
v_hasTrace_432_ = lean_ctor_get_uint8(v_options_431_, sizeof(void*)*1);
if (v_hasTrace_432_ == 0)
{
lean_dec(v_a_424_);
lean_dec(v_declName_410_);
goto v___jp_411_;
}
else
{
lean_object* v_inheritedTraceOptions_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_inheritedTraceOptions_433_ = lean_ctor_get(v_toCold_430_, 11);
v___x_434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_433_, v_options_431_, v___x_435_);
if (v___x_436_ == 0)
{
lean_dec(v_a_424_);
lean_dec(v_declName_410_);
goto v___jp_411_;
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4);
v___x_438_ = l_Lean_MessageData_ofConstName(v_declName_410_, v___x_429_);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Lean_Exception_toMessageData(v_a_424_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v___x_434_, v___x_443_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v___x_446_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v_a_445_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
v___y_396_ = v___x_446_;
goto v___jp_395_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_447_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_444_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_444_);
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
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v_declName_410_);
if (v_isShared_427_ == 0)
{
v___x_456_ = v___x_426_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_424_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v_declName_410_);
if (v_isShared_427_ == 0)
{
v___x_459_ = v___x_426_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_424_);
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
v___jp_411_:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_box(0);
v___x_413_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v___x_412_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
v___y_396_ = v___x_413_;
goto v___jp_395_;
}
}
else
{
lean_object* v_toCold_462_; lean_object* v_options_463_; uint8_t v_hasTrace_464_; 
v_toCold_462_ = lean_ctor_get(v_a_392_, 0);
v_options_463_ = lean_ctor_get(v_toCold_462_, 2);
v_hasTrace_464_ = lean_ctor_get_uint8(v_options_463_, sizeof(void*)*1);
if (v_hasTrace_464_ == 0)
{
lean_dec_ref(v_thm_389_);
goto v___jp_406_;
}
else
{
lean_object* v_origin_465_; lean_object* v_inheritedTraceOptions_466_; lean_object* v_cls_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_origin_465_ = lean_ctor_get(v_thm_389_, 4);
lean_inc_ref(v_origin_465_);
lean_dec_ref(v_thm_389_);
v_inheritedTraceOptions_466_ = lean_ctor_get(v_toCold_462_, 11);
v_cls_467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_468_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_469_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_466_, v_options_463_, v___x_468_);
if (v___x_469_ == 0)
{
lean_dec_ref(v_origin_465_);
goto v___jp_406_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4);
v___x_471_ = l_Lean_Meta_Origin_key(v_origin_465_);
lean_dec_ref(v_origin_465_);
v___x_472_ = l_Lean_MessageData_ofName(v___x_471_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_470_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_467_, v___x_475_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_dec_ref_known(v___x_476_, 1);
goto v___jp_406_;
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
}
v___jp_395_:
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v_a_397_ = lean_ctor_get(v___y_396_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___y_396_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v___y_396_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___y_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_a_401_; lean_object* v___x_403_; 
v_a_401_ = lean_ctor_get(v_a_397_, 0);
lean_inc(v_a_401_);
lean_dec(v_a_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v_a_401_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
v___jp_406_:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___boxed(lean_object* v_thm_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(v_thm_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(lean_object* v___y_492_, uint8_t v_isExporting_493_, lean_object* v___x_494_, lean_object* v___y_495_, lean_object* v___x_496_, lean_object* v_a_x3f_497_){
_start:
{
lean_object* v___x_499_; lean_object* v_env_500_; lean_object* v_nextMacroScope_501_; lean_object* v_ngen_502_; lean_object* v_auxDeclNGen_503_; lean_object* v_traceState_504_; lean_object* v_recordedDeps_505_; lean_object* v_messages_506_; lean_object* v_infoState_507_; lean_object* v_snapshotTasks_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_533_; 
v___x_499_ = lean_st_ref_take(v___y_492_);
v_env_500_ = lean_ctor_get(v___x_499_, 0);
v_nextMacroScope_501_ = lean_ctor_get(v___x_499_, 1);
v_ngen_502_ = lean_ctor_get(v___x_499_, 2);
v_auxDeclNGen_503_ = lean_ctor_get(v___x_499_, 3);
v_traceState_504_ = lean_ctor_get(v___x_499_, 4);
v_recordedDeps_505_ = lean_ctor_get(v___x_499_, 6);
v_messages_506_ = lean_ctor_get(v___x_499_, 7);
v_infoState_507_ = lean_ctor_get(v___x_499_, 8);
v_snapshotTasks_508_ = lean_ctor_get(v___x_499_, 9);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v___x_499_, 5);
lean_dec(v_unused_534_);
v___x_510_ = v___x_499_;
v_isShared_511_ = v_isSharedCheck_533_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snapshotTasks_508_);
lean_inc(v_infoState_507_);
lean_inc(v_messages_506_);
lean_inc(v_recordedDeps_505_);
lean_inc(v_traceState_504_);
lean_inc(v_auxDeclNGen_503_);
lean_inc(v_ngen_502_);
lean_inc(v_nextMacroScope_501_);
lean_inc(v_env_500_);
lean_dec(v___x_499_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_533_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = l_Lean_Environment_setExporting(v_env_500_, v_isExporting_493_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 5, v___x_494_);
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_nextMacroScope_501_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_ngen_502_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_auxDeclNGen_503_);
lean_ctor_set(v_reuseFailAlloc_532_, 4, v_traceState_504_);
lean_ctor_set(v_reuseFailAlloc_532_, 5, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_532_, 6, v_recordedDeps_505_);
lean_ctor_set(v_reuseFailAlloc_532_, 7, v_messages_506_);
lean_ctor_set(v_reuseFailAlloc_532_, 8, v_infoState_507_);
lean_ctor_set(v_reuseFailAlloc_532_, 9, v_snapshotTasks_508_);
v___x_514_ = v_reuseFailAlloc_532_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v_mctx_517_; lean_object* v_zetaDeltaFVarIds_518_; lean_object* v_postponed_519_; lean_object* v_diag_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_530_; 
v___x_515_ = lean_st_ref_put(v___y_492_, v___x_514_);
v___x_516_ = lean_st_ref_take(v___y_495_);
v_mctx_517_ = lean_ctor_get(v___x_516_, 0);
v_zetaDeltaFVarIds_518_ = lean_ctor_get(v___x_516_, 2);
v_postponed_519_ = lean_ctor_get(v___x_516_, 3);
v_diag_520_ = lean_ctor_get(v___x_516_, 4);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v___x_516_, 1);
lean_dec(v_unused_531_);
v___x_522_ = v___x_516_;
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_diag_520_);
lean_inc(v_postponed_519_);
lean_inc(v_zetaDeltaFVarIds_518_);
lean_inc(v_mctx_517_);
lean_dec(v___x_516_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_box(0);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_496_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_mctx_517_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_zetaDeltaFVarIds_518_);
lean_ctor_set(v_reuseFailAlloc_529_, 3, v_postponed_519_);
lean_ctor_set(v_reuseFailAlloc_529_, 4, v_diag_520_);
v___x_526_ = v_reuseFailAlloc_529_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_st_ref_put(v___y_495_, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_524_);
return v___x_528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0___boxed(lean_object* v___y_535_, lean_object* v_isExporting_536_, lean_object* v___x_537_, lean_object* v___y_538_, lean_object* v___x_539_, lean_object* v_a_x3f_540_, lean_object* v___y_541_){
_start:
{
uint8_t v_isExporting_boxed_542_; lean_object* v_res_543_; 
v_isExporting_boxed_542_ = lean_unbox(v_isExporting_536_);
v_res_543_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_535_, v_isExporting_boxed_542_, v___x_537_, v___y_538_, v___x_539_, v_a_x3f_540_);
lean_dec(v_a_x3f_540_);
lean_dec(v___y_538_);
lean_dec(v___y_535_);
return v_res_543_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0);
v___x_549_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
lean_ctor_set(v___x_549_, 2, v___x_548_);
lean_ctor_set(v___x_549_, 3, v___x_548_);
lean_ctor_set(v___x_549_, 4, v___x_548_);
lean_ctor_set(v___x_549_, 5, v___x_548_);
lean_ctor_set(v___x_549_, 6, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(lean_object* v_x_550_, uint8_t v_isExporting_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; lean_object* v_env_558_; lean_object* v___x_559_; uint8_t v_isModule_560_; 
v___x_557_ = lean_st_ref_get(v___y_555_);
v_env_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc_ref(v_env_558_);
lean_dec(v___x_557_);
v___x_559_ = l_Lean_Environment_header(v_env_558_);
v_isModule_560_ = lean_ctor_get_uint8(v___x_559_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_559_);
if (v_isModule_560_ == 0)
{
lean_object* v___x_561_; 
lean_dec_ref(v_env_558_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
v___x_561_ = lean_apply_5(v_x_550_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
return v___x_561_;
}
else
{
uint8_t v_isExporting_562_; 
v_isExporting_562_ = lean_ctor_get_uint8(v_env_558_, sizeof(void*)*13);
lean_dec_ref(v_env_558_);
if (v_isExporting_551_ == 0)
{
if (v_isExporting_562_ == 0)
{
lean_object* v___x_629_; 
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
v___x_629_ = lean_apply_5(v_x_550_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
return v___x_629_;
}
else
{
goto v___jp_563_;
}
}
else
{
if (v_isExporting_562_ == 0)
{
goto v___jp_563_;
}
else
{
lean_object* v___x_630_; 
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
v___x_630_ = lean_apply_5(v_x_550_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
return v___x_630_;
}
}
v___jp_563_:
{
lean_object* v___x_564_; lean_object* v_env_565_; lean_object* v_nextMacroScope_566_; lean_object* v_ngen_567_; lean_object* v_auxDeclNGen_568_; lean_object* v_traceState_569_; lean_object* v_recordedDeps_570_; lean_object* v_messages_571_; lean_object* v_infoState_572_; lean_object* v_snapshotTasks_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_627_; 
v___x_564_ = lean_st_ref_take(v___y_555_);
v_env_565_ = lean_ctor_get(v___x_564_, 0);
v_nextMacroScope_566_ = lean_ctor_get(v___x_564_, 1);
v_ngen_567_ = lean_ctor_get(v___x_564_, 2);
v_auxDeclNGen_568_ = lean_ctor_get(v___x_564_, 3);
v_traceState_569_ = lean_ctor_get(v___x_564_, 4);
v_recordedDeps_570_ = lean_ctor_get(v___x_564_, 6);
v_messages_571_ = lean_ctor_get(v___x_564_, 7);
v_infoState_572_ = lean_ctor_get(v___x_564_, 8);
v_snapshotTasks_573_ = lean_ctor_get(v___x_564_, 9);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_564_, 5);
lean_dec(v_unused_628_);
v___x_575_ = v___x_564_;
v_isShared_576_ = v_isSharedCheck_627_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_snapshotTasks_573_);
lean_inc(v_infoState_572_);
lean_inc(v_messages_571_);
lean_inc(v_recordedDeps_570_);
lean_inc(v_traceState_569_);
lean_inc(v_auxDeclNGen_568_);
lean_inc(v_ngen_567_);
lean_inc(v_nextMacroScope_566_);
lean_inc(v_env_565_);
lean_dec(v___x_564_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_627_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = l_Lean_Environment_setExporting(v_env_565_, v_isExporting_551_);
v___x_578_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 5, v___x_578_);
lean_ctor_set(v___x_575_, 0, v___x_577_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_nextMacroScope_566_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_ngen_567_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_auxDeclNGen_568_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_traceState_569_);
lean_ctor_set(v_reuseFailAlloc_626_, 5, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_626_, 6, v_recordedDeps_570_);
lean_ctor_set(v_reuseFailAlloc_626_, 7, v_messages_571_);
lean_ctor_set(v_reuseFailAlloc_626_, 8, v_infoState_572_);
lean_ctor_set(v_reuseFailAlloc_626_, 9, v_snapshotTasks_573_);
v___x_580_ = v_reuseFailAlloc_626_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_mctx_583_; lean_object* v_zetaDeltaFVarIds_584_; lean_object* v_postponed_585_; lean_object* v_diag_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_624_; 
v___x_581_ = lean_st_ref_put(v___y_555_, v___x_580_);
v___x_582_ = lean_st_ref_take(v___y_553_);
v_mctx_583_ = lean_ctor_get(v___x_582_, 0);
v_zetaDeltaFVarIds_584_ = lean_ctor_get(v___x_582_, 2);
v_postponed_585_ = lean_ctor_get(v___x_582_, 3);
v_diag_586_ = lean_ctor_get(v___x_582_, 4);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v___x_582_, 1);
lean_dec(v_unused_625_);
v___x_588_ = v___x_582_;
v_isShared_589_ = v_isSharedCheck_624_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_diag_586_);
lean_inc(v_postponed_585_);
lean_inc(v_zetaDeltaFVarIds_584_);
lean_inc(v_mctx_583_);
lean_dec(v___x_582_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_624_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v___x_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_mctx_583_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_zetaDeltaFVarIds_584_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_postponed_585_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v_diag_586_);
v___x_592_ = v_reuseFailAlloc_623_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; lean_object* v_r_594_; 
v___x_593_ = lean_st_ref_put(v___y_553_, v___x_592_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
v_r_594_ = lean_apply_5(v_x_550_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
if (lean_obj_tag(v_r_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_611_; 
v_a_595_ = lean_ctor_get(v_r_594_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_r_594_);
if (v_isSharedCheck_611_ == 0)
{
v___x_597_ = v_r_594_;
v_isShared_598_ = v_isSharedCheck_611_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v_r_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_611_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
lean_inc(v_a_595_);
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 1);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_610_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v___x_601_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_555_, v_isExporting_562_, v___x_578_, v___y_553_, v___x_590_, v___x_600_);
lean_dec_ref(v___x_600_);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_601_, 0);
lean_dec(v_unused_609_);
v___x_603_ = v___x_601_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_dec(v___x_601_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v_a_595_);
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_595_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_a_612_ = lean_ctor_get(v_r_594_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v_r_594_, 1);
v___x_613_ = lean_box(0);
v___x_614_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_555_, v_isExporting_562_, v___x_578_, v___y_553_, v___x_590_, v___x_613_);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_614_, 0);
lean_dec(v_unused_622_);
v___x_616_ = v___x_614_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_dec(v___x_614_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set_tag(v___x_616_, 1);
lean_ctor_set(v___x_616_, 0, v_a_612_);
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_612_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___boxed(lean_object* v_x_631_, lean_object* v_isExporting_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
uint8_t v_isExporting_boxed_638_; lean_object* v_res_639_; 
v_isExporting_boxed_638_ = lean_unbox(v_isExporting_632_);
v_res_639_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_631_, v_isExporting_boxed_638_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(lean_object* v_00_u03b1_640_, lean_object* v_x_641_, uint8_t v_isExporting_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_641_, v_isExporting_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___boxed(lean_object* v_00_u03b1_649_, lean_object* v_x_650_, lean_object* v_isExporting_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v_isExporting_boxed_657_; lean_object* v_res_658_; 
v_isExporting_boxed_657_ = lean_unbox(v_isExporting_651_);
v_res_658_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(v_00_u03b1_649_, v_x_650_, v_isExporting_boxed_657_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(lean_object* v_ext_659_, lean_object* v_b_660_, uint8_t v_kind_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_toCold_666_; lean_object* v_currNamespace_667_; lean_object* v___x_668_; lean_object* v_env_669_; lean_object* v_nextMacroScope_670_; lean_object* v_ngen_671_; lean_object* v_auxDeclNGen_672_; lean_object* v_traceState_673_; lean_object* v_recordedDeps_674_; lean_object* v_messages_675_; lean_object* v_infoState_676_; lean_object* v_snapshotTasks_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_704_; 
v_toCold_666_ = lean_ctor_get(v___y_663_, 0);
v_currNamespace_667_ = lean_ctor_get(v_toCold_666_, 4);
v___x_668_ = lean_st_ref_take(v___y_664_);
v_env_669_ = lean_ctor_get(v___x_668_, 0);
v_nextMacroScope_670_ = lean_ctor_get(v___x_668_, 1);
v_ngen_671_ = lean_ctor_get(v___x_668_, 2);
v_auxDeclNGen_672_ = lean_ctor_get(v___x_668_, 3);
v_traceState_673_ = lean_ctor_get(v___x_668_, 4);
v_recordedDeps_674_ = lean_ctor_get(v___x_668_, 6);
v_messages_675_ = lean_ctor_get(v___x_668_, 7);
v_infoState_676_ = lean_ctor_get(v___x_668_, 8);
v_snapshotTasks_677_ = lean_ctor_get(v___x_668_, 9);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_668_, 5);
lean_dec(v_unused_705_);
v___x_679_ = v___x_668_;
v_isShared_680_ = v_isSharedCheck_704_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_snapshotTasks_677_);
lean_inc(v_infoState_676_);
lean_inc(v_messages_675_);
lean_inc(v_recordedDeps_674_);
lean_inc(v_traceState_673_);
lean_inc(v_auxDeclNGen_672_);
lean_inc(v_ngen_671_);
lean_inc(v_nextMacroScope_670_);
lean_inc(v_env_669_);
lean_dec(v___x_668_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_704_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
lean_inc(v_currNamespace_667_);
v___x_681_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_669_, v_ext_659_, v_b_660_, v_kind_661_, v_currNamespace_667_);
v___x_682_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 5, v___x_682_);
lean_ctor_set(v___x_679_, 0, v___x_681_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_nextMacroScope_670_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_ngen_671_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_auxDeclNGen_672_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v_traceState_673_);
lean_ctor_set(v_reuseFailAlloc_703_, 5, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_703_, 6, v_recordedDeps_674_);
lean_ctor_set(v_reuseFailAlloc_703_, 7, v_messages_675_);
lean_ctor_set(v_reuseFailAlloc_703_, 8, v_infoState_676_);
lean_ctor_set(v_reuseFailAlloc_703_, 9, v_snapshotTasks_677_);
v___x_684_ = v_reuseFailAlloc_703_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_mctx_687_; lean_object* v_zetaDeltaFVarIds_688_; lean_object* v_postponed_689_; lean_object* v_diag_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_701_; 
v___x_685_ = lean_st_ref_put(v___y_664_, v___x_684_);
v___x_686_ = lean_st_ref_take(v___y_662_);
v_mctx_687_ = lean_ctor_get(v___x_686_, 0);
v_zetaDeltaFVarIds_688_ = lean_ctor_get(v___x_686_, 2);
v_postponed_689_ = lean_ctor_get(v___x_686_, 3);
v_diag_690_ = lean_ctor_get(v___x_686_, 4);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v___x_686_, 1);
lean_dec(v_unused_702_);
v___x_692_ = v___x_686_;
v_isShared_693_ = v_isSharedCheck_701_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_diag_690_);
lean_inc(v_postponed_689_);
lean_inc(v_zetaDeltaFVarIds_688_);
lean_inc(v_mctx_687_);
lean_dec(v___x_686_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_701_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_694_ = lean_box(0);
v___x_695_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_695_);
v___x_697_ = v___x_692_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_mctx_687_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_zetaDeltaFVarIds_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_postponed_689_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_diag_690_);
v___x_697_ = v_reuseFailAlloc_700_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_st_ref_put(v___y_662_, v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_694_);
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___boxed(lean_object* v_ext_706_, lean_object* v_b_707_, lean_object* v_kind_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v_kind_boxed_713_; lean_object* v_res_714_; 
v_kind_boxed_713_ = lean_unbox(v_kind_708_);
v_res_714_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v_ext_706_, v_b_707_, v_kind_boxed_713_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(lean_object* v_00_u03b1_715_, lean_object* v_00_u03b2_716_, lean_object* v_00_u03c3_717_, lean_object* v_ext_718_, lean_object* v_b_719_, uint8_t v_kind_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v_ext_718_, v_b_719_, v_kind_720_, v___y_722_, v___y_723_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___boxed(lean_object* v_00_u03b1_727_, lean_object* v_00_u03b2_728_, lean_object* v_00_u03c3_729_, lean_object* v_ext_730_, lean_object* v_b_731_, lean_object* v_kind_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v_kind_boxed_738_; lean_object* v_res_739_; 
v_kind_boxed_738_ = lean_unbox(v_kind_732_);
v_res_739_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(v_00_u03b1_727_, v_00_u03b2_728_, v_00_u03c3_729_, v_ext_730_, v_b_731_, v_kind_boxed_738_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(uint8_t v_attrKind_740_, uint8_t v_post_741_, lean_object* v_as_742_, size_t v_sz_743_, size_t v_i_744_, lean_object* v_b_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_a_752_; uint8_t v___x_756_; 
v___x_756_ = lean_usize_dec_lt(v_i_744_, v_sz_743_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v_b_745_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_758_ = lean_box(0);
v_a_759_ = lean_array_uget_borrowed(v_as_742_, v_i_744_);
v___x_760_ = l_Lean_Meta_Grind_normExt;
lean_inc(v_a_759_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v_a_759_);
v___x_762_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_760_, v___x_761_, v_attrKind_740_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_804_; 
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v___x_762_, 0);
lean_dec(v_unused_805_);
v___x_764_ = v___x_762_;
v_isShared_765_ = v_isSharedCheck_804_;
goto v_resetjp_763_;
}
else
{
lean_dec(v___x_762_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_804_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; 
lean_inc(v_a_759_);
v___x_766_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(v_a_759_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
if (lean_obj_tag(v_a_767_) == 1)
{
lean_object* v_val_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_795_; 
v_val_768_ = lean_ctor_get(v_a_767_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_a_767_);
if (v_isSharedCheck_795_ == 0)
{
v___x_770_ = v_a_767_;
v_isShared_771_ = v_isSharedCheck_795_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_val_768_);
lean_dec(v_a_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_795_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___y_774_; 
v___x_772_ = l_Lean_Meta_Grind_normSymExt;
if (v_post_741_ == 0)
{
lean_object* v___x_790_; 
lean_inc(v_val_768_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v_val_768_);
v___x_790_ = v___x_764_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_val_768_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v___y_774_ = v___x_790_;
goto v___jp_773_;
}
}
else
{
lean_object* v___x_793_; 
lean_inc(v_val_768_);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 1);
lean_ctor_set(v___x_764_, 0, v_val_768_);
v___x_793_ = v___x_764_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_val_768_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
v___y_774_ = v___x_793_;
goto v___jp_773_;
}
}
v___jp_773_:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_772_, v___y_774_, v_attrKind_740_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_787_; 
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v___x_775_, 0);
lean_dec(v_unused_788_);
v___x_777_ = v___x_775_;
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
else
{
lean_dec(v___x_775_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
if (v_post_741_ == 0)
{
lean_del_object(v___x_777_);
lean_del_object(v___x_770_);
lean_dec(v_val_768_);
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
else
{
uint8_t v_rfl_779_; 
v_rfl_779_ = lean_ctor_get_uint8(v_a_759_, sizeof(void*)*5 + 2);
if (v_rfl_779_ == 0)
{
lean_del_object(v___x_777_);
lean_del_object(v___x_770_);
lean_dec(v_val_768_);
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
else
{
lean_object* v___x_781_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v_val_768_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_val_768_);
v___x_781_ = v_reuseFailAlloc_786_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set_tag(v___x_770_, 2);
lean_ctor_set(v___x_770_, 0, v___x_781_);
v___x_783_ = v___x_770_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_785_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_772_, v___x_783_, v_attrKind_740_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_dec_ref_known(v___x_784_, 1);
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
else
{
return v___x_784_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_770_);
lean_dec(v_val_768_);
return v___x_775_;
}
}
}
}
else
{
lean_dec(v_a_767_);
lean_del_object(v___x_764_);
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_del_object(v___x_764_);
v_a_796_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_766_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_766_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
else
{
return v___x_762_;
}
}
v___jp_751_:
{
size_t v___x_753_; size_t v___x_754_; 
v___x_753_ = ((size_t)1ULL);
v___x_754_ = lean_usize_add(v_i_744_, v___x_753_);
v_i_744_ = v___x_754_;
v_b_745_ = v_a_752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2___boxed(lean_object* v_attrKind_806_, lean_object* v_post_807_, lean_object* v_as_808_, lean_object* v_sz_809_, lean_object* v_i_810_, lean_object* v_b_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v_attrKind_boxed_817_; uint8_t v_post_boxed_818_; size_t v_sz_boxed_819_; size_t v_i_boxed_820_; lean_object* v_res_821_; 
v_attrKind_boxed_817_ = lean_unbox(v_attrKind_806_);
v_post_boxed_818_ = lean_unbox(v_post_807_);
v_sz_boxed_819_ = lean_unbox_usize(v_sz_809_);
lean_dec(v_sz_809_);
v_i_boxed_820_ = lean_unbox_usize(v_i_810_);
lean_dec(v_i_810_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(v_attrKind_boxed_817_, v_post_boxed_818_, v_as_808_, v_sz_boxed_819_, v_i_boxed_820_, v_b_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v_as_808_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object* v_declName_822_, uint8_t v_post_823_, uint8_t v_inv_824_, uint8_t v_attrKind_825_, lean_object* v_prio_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___y_838_; uint8_t v___x_861_; uint8_t v___x_862_; 
v___x_832_ = 1;
v___x_833_ = lean_box(v_post_823_);
v___x_834_ = lean_box(v_inv_824_);
v___x_835_ = lean_box(v___x_832_);
lean_inc(v_declName_822_);
v___x_836_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpTheoremFromConst___boxed), 10, 5);
lean_closure_set(v___x_836_, 0, v_declName_822_);
lean_closure_set(v___x_836_, 1, v___x_833_);
lean_closure_set(v___x_836_, 2, v___x_834_);
lean_closure_set(v___x_836_, 3, v_prio_826_);
lean_closure_set(v___x_836_, 4, v___x_835_);
v___x_861_ = 1;
v___x_862_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_825_, v___x_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; 
v___x_863_ = l_Lean_isPrivateName(v_declName_822_);
lean_dec(v_declName_822_);
if (v___x_863_ == 0)
{
v___y_838_ = v___x_832_;
goto v___jp_837_;
}
else
{
v___y_838_ = v___x_862_;
goto v___jp_837_;
}
}
else
{
uint8_t v___x_864_; 
lean_dec(v_declName_822_);
v___x_864_ = 0;
v___y_838_ = v___x_864_;
goto v___jp_837_;
}
v___jp_837_:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v___x_836_, v___y_838_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; size_t v_sz_842_; size_t v___x_843_; lean_object* v___x_844_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v___x_841_ = lean_box(0);
v_sz_842_ = lean_array_size(v_a_840_);
v___x_843_ = ((size_t)0ULL);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(v_attrKind_825_, v_post_823_, v_a_840_, v_sz_842_, v___x_843_, v___x_841_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_840_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v___x_844_, 0);
lean_dec(v_unused_852_);
v___x_846_ = v___x_844_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_dec(v___x_844_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_841_);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_841_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
return v___x_844_;
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_839_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_839_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem___boxed(lean_object* v_declName_865_, lean_object* v_post_866_, lean_object* v_inv_867_, lean_object* v_attrKind_868_, lean_object* v_prio_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
uint8_t v_post_boxed_875_; uint8_t v_inv_boxed_876_; uint8_t v_attrKind_boxed_877_; lean_object* v_res_878_; 
v_post_boxed_875_ = lean_unbox(v_post_866_);
v_inv_boxed_876_ = lean_unbox(v_inv_867_);
v_attrKind_boxed_877_ = lean_unbox(v_attrKind_868_);
v_res_878_ = l_Lean_Meta_Grind_addNormTheorem(v_declName_865_, v_post_boxed_875_, v_inv_boxed_876_, v_attrKind_boxed_877_, v_prio_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(uint8_t v_attrKind_879_, lean_object* v_as_880_, size_t v_sz_881_, size_t v_i_882_, lean_object* v_b_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
uint8_t v___x_888_; 
v___x_888_ = lean_usize_dec_lt(v_i_882_, v_sz_881_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v_b_883_);
return v___x_889_;
}
else
{
lean_object* v___x_890_; lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_890_ = lean_box(0);
v_a_891_ = lean_array_uget_borrowed(v_as_880_, v_i_882_);
v___x_892_ = l_Lean_Meta_Grind_normSymExt;
lean_inc(v_a_891_);
v___x_893_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_893_, 0, v_a_891_);
v___x_894_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_892_, v___x_893_, v_attrKind_879_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_894_) == 0)
{
size_t v___x_895_; size_t v___x_896_; 
lean_dec_ref_known(v___x_894_, 1);
v___x_895_ = ((size_t)1ULL);
v___x_896_ = lean_usize_add(v_i_882_, v___x_895_);
v_i_882_ = v___x_896_;
v_b_883_ = v___x_890_;
goto _start;
}
else
{
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg___boxed(lean_object* v_attrKind_898_, lean_object* v_as_899_, lean_object* v_sz_900_, lean_object* v_i_901_, lean_object* v_b_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v_attrKind_boxed_907_; size_t v_sz_boxed_908_; size_t v_i_boxed_909_; lean_object* v_res_910_; 
v_attrKind_boxed_907_ = lean_unbox(v_attrKind_898_);
v_sz_boxed_908_ = lean_unbox_usize(v_sz_900_);
lean_dec(v_sz_900_);
v_i_boxed_909_ = lean_unbox_usize(v_i_901_);
lean_dec(v_i_901_);
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_boxed_907_, v_as_899_, v_sz_boxed_908_, v_i_boxed_909_, v_b_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v_as_899_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(lean_object* v_declName_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v_env_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_914_ = lean_st_ref_get(v___y_912_);
v_env_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc_ref(v_env_915_);
lean_dec(v___x_914_);
v___x_916_ = l_Lean_getReducibilityStatusCore(v_env_915_, v_declName_911_);
v___x_917_ = lean_box(v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg___boxed(lean_object* v_declName_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_919_, v___y_920_);
lean_dec(v___y_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(lean_object* v_declName_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_945_; 
v___x_929_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_923_, v___y_927_);
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_945_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_945_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_945_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
uint8_t v___x_934_; 
v___x_934_ = lean_unbox(v_a_930_);
lean_dec(v_a_930_);
if (v___x_934_ == 0)
{
uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_935_ = 1;
v___x_936_ = lean_box(v___x_935_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_936_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = 0;
v___x_941_ = lean_box(v___x_940_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_941_);
v___x_943_ = v___x_932_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0___boxed(lean_object* v_declName_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(v_declName_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(uint8_t v_attrKind_953_, lean_object* v_as_954_, size_t v_sz_955_, size_t v_i_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_usize_dec_lt(v_i_956_, v_sz_955_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_b_957_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_964_ = lean_box(0);
v_a_965_ = lean_array_uget_borrowed(v_as_954_, v_i_956_);
v___x_966_ = l_Lean_Meta_Grind_normSymExt;
lean_inc(v_a_965_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v_a_965_);
v___x_968_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_966_, v___x_967_, v_attrKind_953_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_968_) == 0)
{
size_t v___x_969_; size_t v___x_970_; 
lean_dec_ref_known(v___x_968_, 1);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_add(v_i_956_, v___x_969_);
v_i_956_ = v___x_970_;
v_b_957_ = v___x_964_;
goto _start;
}
else
{
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg___boxed(lean_object* v_attrKind_972_, lean_object* v_as_973_, lean_object* v_sz_974_, lean_object* v_i_975_, lean_object* v_b_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v_attrKind_boxed_981_; size_t v_sz_boxed_982_; size_t v_i_boxed_983_; lean_object* v_res_984_; 
v_attrKind_boxed_981_ = lean_unbox(v_attrKind_972_);
v_sz_boxed_982_ = lean_unbox_usize(v_sz_974_);
lean_dec(v_sz_974_);
v_i_boxed_983_ = lean_unbox_usize(v_i_975_);
lean_dec(v_i_975_);
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_boxed_981_, v_as_973_, v_sz_boxed_982_, v_i_boxed_983_, v_b_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v_as_973_);
return v_res_984_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold(lean_object* v_declName_988_, uint8_t v_attrKind_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_998_; 
lean_inc(v_declName_988_);
v___x_998_ = l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(v_declName_988_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1065_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1065_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1065_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___y_1004_; lean_object* v_a_1005_; uint8_t v___x_1024_; 
v___x_1024_ = lean_unbox(v_a_999_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_del_object(v___x_1001_);
lean_inc(v_declName_988_);
v___x_1025_ = l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(v_declName_988_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; size_t v_sz_1028_; size_t v___x_1029_; lean_object* v___x_1030_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = lean_box(0);
v_sz_1028_ = lean_array_size(v_a_1026_);
v___x_1029_ = ((size_t)0ULL);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_989_, v_a_1026_, v_sz_1028_, v___x_1029_, v___x_1027_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_1026_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1031_; 
lean_dec_ref_known(v___x_1030_, 1);
lean_inc(v_declName_988_);
v___x_1031_ = l_Lean_Meta_Sym_DSimp_Decls_mkEntries(v_declName_988_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; size_t v_sz_1033_; lean_object* v___x_1034_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v_sz_1033_ = lean_array_size(v_a_1032_);
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_989_, v_a_1032_, v_sz_1033_, v___x_1029_, v___x_1027_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_1032_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; 
v_unused_1042_ = lean_ctor_get(v___x_1034_, 0);
lean_dec(v_unused_1042_);
v___x_1036_ = v___x_1034_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v___x_1034_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1027_);
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1027_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
else
{
lean_object* v_a_1043_; 
v_a_1043_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1043_);
v___y_1004_ = v___x_1034_;
v_a_1005_ = v_a_1043_;
goto v___jp_1003_;
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1031_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1031_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
lean_inc(v_a_1044_);
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
v___y_1004_ = v___x_1049_;
v_a_1005_ = v_a_1044_;
goto v___jp_1003_;
}
}
}
}
else
{
lean_object* v_a_1052_; 
v_a_1052_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1052_);
v___y_1004_ = v___x_1030_;
v_a_1005_ = v_a_1052_;
goto v___jp_1003_;
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1025_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1025_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
lean_inc(v_a_1053_);
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
v___y_1004_ = v___x_1058_;
v_a_1005_ = v_a_1053_;
goto v___jp_1003_;
}
}
}
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
v___x_1061_ = lean_box(0);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1061_);
v___x_1063_ = v___x_1001_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
v___jp_1003_:
{
uint8_t v___x_1006_; 
v___x_1006_ = l_Lean_Exception_isInterrupt(v_a_1005_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; 
lean_inc_ref(v_a_1005_);
v___x_1007_ = l_Lean_Exception_isRuntime(v_a_1005_);
if (v___x_1007_ == 0)
{
lean_object* v_toCold_1008_; lean_object* v_options_1009_; uint8_t v_hasTrace_1010_; 
lean_dec_ref(v___y_1004_);
v_toCold_1008_ = lean_ctor_get(v_a_992_, 0);
v_options_1009_ = lean_ctor_get(v_toCold_1008_, 2);
v_hasTrace_1010_ = lean_ctor_get_uint8(v_options_1009_, sizeof(void*)*1);
if (v_hasTrace_1010_ == 0)
{
lean_dec_ref(v_a_1005_);
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
goto v___jp_995_;
}
else
{
lean_object* v_inheritedTraceOptions_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_inheritedTraceOptions_1011_ = lean_ctor_get(v_toCold_1008_, 11);
v___x_1012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_1013_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_1014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1011_, v_options_1009_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_dec_ref(v_a_1005_);
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
goto v___jp_995_;
}
else
{
lean_object* v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1015_ = lean_obj_once(&l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1, &l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1_once, _init_l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1);
v___x_1016_ = lean_unbox(v_a_999_);
lean_dec(v_a_999_);
v___x_1017_ = l_Lean_MessageData_ofConstName(v_declName_988_, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1015_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_Exception_toMessageData(v_a_1005_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v___x_1012_, v___x_1022_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_1023_;
}
}
}
else
{
lean_dec_ref(v_a_1005_);
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
return v___y_1004_;
}
}
else
{
lean_dec_ref(v_a_1005_);
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
return v___y_1004_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_declName_988_);
v_a_1066_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_998_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_998_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
v___jp_995_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_box(0);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___boxed(lean_object* v_declName_1074_, lean_object* v_attrKind_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
uint8_t v_attrKind_boxed_1081_; lean_object* v_res_1082_; 
v_attrKind_boxed_1081_ = lean_unbox(v_attrKind_1075_);
v_res_1082_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v_declName_1074_, v_attrKind_boxed_1081_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(lean_object* v_declName_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_1083_, v___y_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___boxed(lean_object* v_declName_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(v_declName_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(uint8_t v_attrKind_1097_, lean_object* v_as_1098_, size_t v_sz_1099_, size_t v_i_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_1097_, v_as_1098_, v_sz_1099_, v_i_1100_, v_b_1101_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___boxed(lean_object* v_attrKind_1108_, lean_object* v_as_1109_, lean_object* v_sz_1110_, lean_object* v_i_1111_, lean_object* v_b_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v_attrKind_boxed_1118_; size_t v_sz_boxed_1119_; size_t v_i_boxed_1120_; lean_object* v_res_1121_; 
v_attrKind_boxed_1118_ = lean_unbox(v_attrKind_1108_);
v_sz_boxed_1119_ = lean_unbox_usize(v_sz_1110_);
lean_dec(v_sz_1110_);
v_i_boxed_1120_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_res_1121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(v_attrKind_boxed_1118_, v_as_1109_, v_sz_boxed_1119_, v_i_boxed_1120_, v_b_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v_as_1109_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(uint8_t v_attrKind_1122_, lean_object* v_as_1123_, size_t v_sz_1124_, size_t v_i_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_1122_, v_as_1123_, v_sz_1124_, v_i_1125_, v_b_1126_, v___y_1128_, v___y_1129_, v___y_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___boxed(lean_object* v_attrKind_1133_, lean_object* v_as_1134_, lean_object* v_sz_1135_, lean_object* v_i_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v_attrKind_boxed_1143_; size_t v_sz_boxed_1144_; size_t v_i_boxed_1145_; lean_object* v_res_1146_; 
v_attrKind_boxed_1143_ = lean_unbox(v_attrKind_1133_);
v_sz_boxed_1144_ = lean_unbox_usize(v_sz_1135_);
lean_dec(v_sz_1135_);
v_i_boxed_1145_ = lean_unbox_usize(v_i_1136_);
lean_dec(v_i_1136_);
v_res_1146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(v_attrKind_boxed_1143_, v_as_1134_, v_sz_boxed_1144_, v_i_boxed_1145_, v_b_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec_ref(v_as_1134_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold(lean_object* v_declName_1147_, uint8_t v_attrKind_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1154_ = l_Lean_Meta_Grind_normExt;
v___x_1155_ = 0;
v___x_1156_ = lean_unsigned_to_nat(1000u);
lean_inc(v_declName_1147_);
v___x_1157_ = l_Lean_Meta_addDeclToUnfold(v___x_1154_, v_declName_1147_, v___x_1155_, v___x_1155_, v___x_1156_, v_attrKind_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1184_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1184_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1184_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_unbox(v_a_1158_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_dec(v_a_1158_);
lean_dec(v_declName_1147_);
v___x_1163_ = lean_box(v___x_1155_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1163_);
v___x_1165_ = v___x_1160_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
else
{
lean_object* v___x_1167_; 
lean_del_object(v___x_1160_);
v___x_1167_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v_declName_1147_, v_attrKind_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v___x_1167_, 0);
lean_dec(v_unused_1175_);
v___x_1169_ = v___x_1167_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_dec(v___x_1167_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v_a_1158_);
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1158_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_a_1158_);
v_a_1176_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1167_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1167_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_1147_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold___boxed(lean_object* v_declName_1185_, lean_object* v_attrKind_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v_attrKind_boxed_1192_; lean_object* v_res_1193_; 
v_attrKind_boxed_1192_ = lean_unbox(v_attrKind_1186_);
v_res_1193_ = l_Lean_Meta_Grind_addNormDeclToUnfold(v_declName_1185_, v_attrKind_boxed_1192_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object* v_x_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_obj_tag_nat(v_x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object* v_x_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(v_x_1196_);
lean_dec(v_x_1196_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_1198_, lean_object* v_k_1199_){
_start:
{
switch(lean_obj_tag(v_t_1198_))
{
case 0:
{
lean_object* v_k_1200_; lean_object* v___x_1201_; 
v_k_1200_ = lean_ctor_get(v_t_1198_, 0);
lean_inc(v_k_1200_);
lean_dec_ref_known(v_t_1198_, 1);
v___x_1201_ = lean_apply_1(v_k_1199_, v_k_1200_);
return v___x_1201_;
}
case 1:
{
uint8_t v_eager_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_eager_1202_ = lean_ctor_get_uint8(v_t_1198_, 0);
lean_dec_ref_known(v_t_1198_, 0);
v___x_1203_ = lean_box(v_eager_1202_);
v___x_1204_ = lean_apply_1(v_k_1199_, v___x_1203_);
return v___x_1204_;
}
case 5:
{
lean_object* v_prio_1205_; lean_object* v___x_1206_; 
v_prio_1205_ = lean_ctor_get(v_t_1198_, 0);
lean_inc(v_prio_1205_);
lean_dec_ref_known(v_t_1198_, 1);
v___x_1206_ = lean_apply_1(v_k_1199_, v_prio_1205_);
return v___x_1206_;
}
case 8:
{
uint8_t v_post_1207_; uint8_t v_inv_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_post_1207_ = lean_ctor_get_uint8(v_t_1198_, 0);
v_inv_1208_ = lean_ctor_get_uint8(v_t_1198_, 1);
lean_dec_ref_known(v_t_1198_, 0);
v___x_1209_ = lean_box(v_post_1207_);
v___x_1210_ = lean_box(v_inv_1208_);
v___x_1211_ = lean_apply_2(v_k_1199_, v___x_1209_, v___x_1210_);
return v___x_1211_;
}
case 10:
{
uint8_t v_fallback_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_fallback_1212_ = lean_ctor_get_uint8(v_t_1198_, 0);
lean_dec_ref_known(v_t_1198_, 0);
v___x_1213_ = lean_box(v_fallback_1212_);
v___x_1214_ = lean_apply_1(v_k_1199_, v___x_1213_);
return v___x_1214_;
}
default: 
{
lean_dec(v_t_1198_);
return v_k_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_1215_, lean_object* v_ctorIdx_1216_, lean_object* v_t_1217_, lean_object* v_h_1218_, lean_object* v_k_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1217_, v_k_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_1221_, lean_object* v_ctorIdx_1222_, lean_object* v_t_1223_, lean_object* v_h_1224_, lean_object* v_k_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_1221_, v_ctorIdx_1222_, v_t_1223_, v_h_1224_, v_k_1225_);
lean_dec(v_ctorIdx_1222_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_1227_, lean_object* v_ematch_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1227_, v_ematch_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_1230_, lean_object* v_t_1231_, lean_object* v_h_1232_, lean_object* v_ematch_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1231_, v_ematch_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_1235_, lean_object* v_cases_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1235_, v_cases_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_1238_, lean_object* v_t_1239_, lean_object* v_h_1240_, lean_object* v_cases_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1239_, v_cases_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_1243_, lean_object* v_intro_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1243_, v_intro_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_1246_, lean_object* v_t_1247_, lean_object* v_h_1248_, lean_object* v_intro_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1247_, v_intro_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_1251_, lean_object* v_infer_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1251_, v_infer_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_1254_, lean_object* v_t_1255_, lean_object* v_h_1256_, lean_object* v_infer_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1255_, v_infer_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_1259_, lean_object* v_ext_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1259_, v_ext_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_1262_, lean_object* v_t_1263_, lean_object* v_h_1264_, lean_object* v_ext_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1263_, v_ext_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_1267_, lean_object* v_symbol_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1267_, v_symbol_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_1270_, lean_object* v_t_1271_, lean_object* v_h_1272_, lean_object* v_symbol_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1271_, v_symbol_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_1275_, lean_object* v_inj_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1275_, v_inj_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_1278_, lean_object* v_t_1279_, lean_object* v_h_1280_, lean_object* v_inj_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1279_, v_inj_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_1283_, lean_object* v_funCC_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1283_, v_funCC_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_1286_, lean_object* v_t_1287_, lean_object* v_h_1288_, lean_object* v_funCC_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1287_, v_funCC_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_1291_, lean_object* v_norm_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1291_, v_norm_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_1294_, lean_object* v_t_1295_, lean_object* v_h_1296_, lean_object* v_norm_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1295_, v_norm_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_1299_, lean_object* v_unfold_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1299_, v_unfold_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_1302_, lean_object* v_t_1303_, lean_object* v_h_1304_, lean_object* v_unfold_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1303_, v_unfold_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_1307_, lean_object* v_homo_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1307_, v_homo_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_1310_, lean_object* v_t_1311_, lean_object* v_h_1312_, lean_object* v_homo_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1311_, v_homo_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_1315_, lean_object* v_homoPred_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1315_, v_homoPred_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_1318_, lean_object* v_t_1319_, lean_object* v_h_1320_, lean_object* v_homoPred_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1319_, v_homoPred_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1325_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1326_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
lean_ctor_set(v___x_1328_, 2, v___x_1327_);
lean_ctor_set(v___x_1328_, 3, v___x_1327_);
lean_ctor_set(v___x_1328_, 4, v___x_1326_);
lean_ctor_set(v___x_1328_, 5, v___x_1326_);
lean_ctor_set(v___x_1328_, 6, v___x_1326_);
lean_ctor_set(v___x_1328_, 7, v___x_1326_);
lean_ctor_set(v___x_1328_, 8, v___x_1326_);
lean_ctor_set(v___x_1328_, 9, v___x_1326_);
lean_ctor_set(v___x_1328_, 10, v___x_1326_);
lean_ctor_set(v___x_1328_, 11, v___x_1325_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = lean_unsigned_to_nat(32u);
v___x_1330_ = lean_mk_empty_array_with_capacity(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1332_ = ((size_t)5ULL);
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_unsigned_to_nat(32u);
v___x_1335_ = lean_mk_empty_array_with_capacity(v___x_1334_);
v___x_1336_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_1337_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___x_1335_);
lean_ctor_set(v___x_1337_, 2, v___x_1333_);
lean_ctor_set(v___x_1337_, 3, v___x_1333_);
lean_ctor_set_usize(v___x_1337_, 4, v___x_1332_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1338_ = lean_box(1);
v___x_1339_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_1340_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_1341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v___x_1339_);
lean_ctor_set(v___x_1341_, 2, v___x_1338_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v_toCold_1347_; lean_object* v_env_1348_; lean_object* v_options_1349_; uint8_t v___x_1350_; lean_object* v_env_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1346_ = lean_st_ref_get(v___y_1344_);
v_toCold_1347_ = lean_ctor_get(v___y_1343_, 0);
v_env_1348_ = lean_ctor_get(v___x_1346_, 0);
lean_inc_ref(v_env_1348_);
lean_dec(v___x_1346_);
v_options_1349_ = lean_ctor_get(v_toCold_1347_, 2);
v___x_1350_ = 0;
v_env_1351_ = l_Lean_Environment_setRecordingDeps(v_env_1348_, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_1353_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_1349_);
v___x_1354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1354_, 0, v_env_1351_);
lean_ctor_set(v___x_1354_, 1, v___x_1352_);
lean_ctor_set(v___x_1354_, 2, v___x_1353_);
lean_ctor_set(v___x_1354_, 3, v_options_1349_);
v___x_1355_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_msgData_1342_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_ref_1366_; lean_object* v___x_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_ref_1366_ = lean_ctor_get(v___y_1363_, 2);
v___x_1367_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_1362_, v___y_1363_, v___y_1364_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_inc(v_ref_1366_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_ref_1366_);
lean_ctor_set(v___x_1372_, 1, v_a_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 1);
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_1382_, lean_object* v_msg_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_toCold_1387_; lean_object* v_currRecDepth_1388_; lean_object* v_ref_1389_; uint16_t v_optionFlags_1390_; uint8_t v_suppressElabErrors_1391_; uint8_t v_checkDeprecated_1392_; uint8_t v_isRecordingDeps_1393_; lean_object* v_ref_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_toCold_1387_ = lean_ctor_get(v___y_1384_, 0);
v_currRecDepth_1388_ = lean_ctor_get(v___y_1384_, 1);
v_ref_1389_ = lean_ctor_get(v___y_1384_, 2);
v_optionFlags_1390_ = lean_ctor_get_uint16(v___y_1384_, sizeof(void*)*3);
v_suppressElabErrors_1391_ = lean_ctor_get_uint8(v___y_1384_, sizeof(void*)*3 + 2);
v_checkDeprecated_1392_ = lean_ctor_get_uint8(v___y_1384_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1393_ = lean_ctor_get_uint8(v___y_1384_, sizeof(void*)*3 + 4);
v_ref_1394_ = l_Lean_replaceRef(v_ref_1382_, v_ref_1389_);
lean_inc(v_currRecDepth_1388_);
lean_inc_ref(v_toCold_1387_);
v___x_1395_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1395_, 0, v_toCold_1387_);
lean_ctor_set(v___x_1395_, 1, v_currRecDepth_1388_);
lean_ctor_set(v___x_1395_, 2, v_ref_1394_);
lean_ctor_set_uint16(v___x_1395_, sizeof(void*)*3, v_optionFlags_1390_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*3 + 2, v_suppressElabErrors_1391_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*3 + 3, v_checkDeprecated_1392_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*3 + 4, v_isRecordingDeps_1393_);
v___x_1396_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1383_, v___x_1395_, v___y_1385_);
lean_dec_ref_known(v___x_1395_, 3);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_1397_, lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_1397_, v_msg_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v_ref_1397_);
return v_res_1402_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4(void){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
v___x_1412_ = l_Lean_stringToMessageData(v___x_1411_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__5));
v___x_1415_ = l_Lean_stringToMessageData(v___x_1414_);
return v___x_1415_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__54(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__53));
v___x_1556_ = l_Lean_stringToMessageData(v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1587_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__2));
lean_inc(v_stx_1583_);
v___x_1588_ = l_Lean_Syntax_isOfKind(v_stx_1583_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1589_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1590_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1593_, v_a_1584_, v_a_1585_);
return v___x_1594_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = l_Lean_Syntax_getArg(v_stx_1583_, v___x_1595_);
v___x_1597_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__8));
lean_inc(v___x_1596_);
v___x_1598_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__10));
lean_inc(v___x_1596_);
v___x_1600_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__12));
lean_inc(v___x_1596_);
v___x_1602_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__14));
lean_inc(v___x_1596_);
v___x_1604_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__16));
lean_inc(v___x_1596_);
v___x_1606_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__18));
lean_inc(v___x_1596_);
v___x_1608_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__20));
lean_inc(v___x_1596_);
v___x_1610_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__22));
lean_inc(v___x_1596_);
v___x_1612_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__24));
lean_inc(v___x_1596_);
v___x_1614_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__26));
lean_inc(v___x_1596_);
v___x_1616_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
lean_inc(v___x_1596_);
v___x_1618_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__30));
lean_inc(v___x_1596_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__32));
lean_inc(v___x_1596_);
v___x_1622_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__34));
lean_inc(v___x_1596_);
v___x_1624_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__36));
lean_inc(v___x_1596_);
v___x_1626_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__38));
lean_inc(v___x_1596_);
v___x_1628_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__40));
lean_inc(v___x_1596_);
v___x_1630_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__42));
lean_inc(v___x_1596_);
v___x_1632_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__44));
lean_inc(v___x_1596_);
v___x_1634_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__46));
lean_inc(v___x_1596_);
v___x_1636_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__48));
lean_inc(v___x_1596_);
v___x_1638_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__50));
lean_inc(v___x_1596_);
v___x_1640_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__52));
lean_inc(v___x_1596_);
v___x_1642_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec(v___x_1596_);
v___x_1643_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1644_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1647_, v_a_1584_, v_a_1585_);
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v_stx_1583_);
v___x_1649_ = lean_unsigned_to_nat(1u);
v___x_1650_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1649_);
lean_dec(v___x_1596_);
v___x_1651_ = l_Lean_Syntax_isNatLit_x3f(v___x_1650_);
if (lean_obj_tag(v___x_1651_) == 1)
{
lean_object* v_val_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v___x_1650_);
v_val_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1660_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_val_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1660_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set_tag(v___x_1654_, 5);
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_val_1652_);
v___x_1657_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_dec(v___x_1651_);
v___x_1661_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__54, &l_Lean_Meta_Grind_getAttrKindCore___closed__54_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__54);
v___x_1662_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_1650_, v___x_1661_, v_a_1584_, v_a_1585_);
lean_dec(v___x_1650_);
return v___x_1662_;
}
}
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1663_ = lean_box(11);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
return v___x_1664_;
}
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1665_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_1665_, 0, v___x_1588_);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1667_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_1667_, 0, v___x_1634_);
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1669_ = lean_box(9);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1671_);
lean_inc(v___x_1672_);
v___x_1673_ = l_Lean_Syntax_matchesNull(v___x_1672_, v___x_1595_);
if (v___x_1673_ == 0)
{
uint8_t v___x_1674_; 
lean_inc(v___x_1672_);
v___x_1674_ = l_Lean_Syntax_matchesNull(v___x_1672_, v___x_1671_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v___x_1672_);
lean_dec(v___x_1596_);
v___x_1675_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1676_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1679_, v_a_1584_, v_a_1585_);
return v___x_1680_;
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1681_ = l_Lean_Syntax_getArg(v___x_1672_, v___x_1595_);
lean_dec(v___x_1672_);
v___x_1682_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
lean_inc(v___x_1681_);
v___x_1683_ = l_Lean_Syntax_isOfKind(v___x_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_1685_ = l_Lean_Syntax_isOfKind(v___x_1681_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v___x_1596_);
v___x_1686_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1687_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1690_, v_a_1584_, v_a_1585_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1692_ = lean_unsigned_to_nat(2u);
v___x_1693_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1692_);
lean_dec(v___x_1596_);
lean_inc(v___x_1693_);
v___x_1694_ = l_Lean_Syntax_matchesNull(v___x_1693_, v___x_1595_);
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; 
v___x_1695_ = l_Lean_Syntax_matchesNull(v___x_1693_, v___x_1671_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1696_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1697_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1700_, v_a_1584_, v_a_1585_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec(v_stx_1583_);
v___x_1702_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1702_, 0, v___x_1694_);
lean_ctor_set_uint8(v___x_1702_, 1, v___x_1588_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
return v___x_1703_;
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v___x_1693_);
lean_dec(v_stx_1583_);
v___x_1704_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1704_, 0, v___x_1683_);
lean_ctor_set_uint8(v___x_1704_, 1, v___x_1683_);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
return v___x_1705_;
}
}
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
lean_dec(v___x_1681_);
v___x_1706_ = lean_unsigned_to_nat(2u);
v___x_1707_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1706_);
lean_dec(v___x_1596_);
lean_inc(v___x_1707_);
v___x_1708_ = l_Lean_Syntax_matchesNull(v___x_1707_, v___x_1595_);
if (v___x_1708_ == 0)
{
uint8_t v___x_1709_; 
v___x_1709_ = l_Lean_Syntax_matchesNull(v___x_1707_, v___x_1671_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1710_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1711_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1712_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1714_, v_a_1584_, v_a_1585_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec(v_stx_1583_);
v___x_1716_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1716_, 0, v___x_1588_);
lean_ctor_set_uint8(v___x_1716_, 1, v___x_1588_);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec(v___x_1707_);
lean_dec(v_stx_1583_);
v___x_1718_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1718_, 0, v___x_1588_);
lean_ctor_set_uint8(v___x_1718_, 1, v___x_1673_);
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
return v___x_1719_;
}
}
}
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
lean_dec(v___x_1672_);
v___x_1720_ = lean_unsigned_to_nat(2u);
v___x_1721_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1720_);
lean_dec(v___x_1596_);
lean_inc(v___x_1721_);
v___x_1722_ = l_Lean_Syntax_matchesNull(v___x_1721_, v___x_1595_);
if (v___x_1722_ == 0)
{
uint8_t v___x_1723_; 
v___x_1723_ = l_Lean_Syntax_matchesNull(v___x_1721_, v___x_1671_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1724_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1725_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1728_, v_a_1584_, v_a_1585_);
return v___x_1729_;
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_stx_1583_);
v___x_1730_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1730_, 0, v___x_1588_);
lean_ctor_set_uint8(v___x_1730_, 1, v___x_1588_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v___x_1721_);
lean_dec(v_stx_1583_);
v___x_1732_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1732_, 0, v___x_1588_);
lean_ctor_set_uint8(v___x_1732_, 1, v___x_1630_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1734_ = lean_box(7);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1736_ = lean_box(6);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1738_ = lean_box(4);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1740_ = lean_box(2);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1742_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1742_, 0, v___x_1588_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1744_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1744_, 0, v___x_1618_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1746_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1746_, 0, v___x_1588_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
return v___x_1748_;
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1749_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1751_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
return v___x_1752_;
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1753_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1755_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1757_ = lean_unsigned_to_nat(3u);
v___x_1758_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1757_);
lean_dec(v___x_1596_);
lean_inc(v___x_1758_);
v___x_1759_ = l_Lean_Syntax_matchesNull(v___x_1758_, v___x_1595_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1758_);
v___x_1761_ = l_Lean_Syntax_matchesNull(v___x_1758_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec(v___x_1758_);
v___x_1762_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1763_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1762_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1764_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1766_, v_a_1584_, v_a_1585_);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1768_ = l_Lean_Syntax_getArg(v___x_1758_, v___x_1595_);
lean_dec(v___x_1758_);
v___x_1769_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1770_ = l_Lean_Syntax_isOfKind(v___x_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1771_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1772_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1775_, v_a_1584_, v_a_1585_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v_stx_1583_);
v___x_1777_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1777_, 0, v___x_1588_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
return v___x_1779_;
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec(v___x_1758_);
lean_dec(v_stx_1583_);
v___x_1780_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1780_, 0, v___x_1606_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1783_ = lean_unsigned_to_nat(2u);
v___x_1784_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1783_);
lean_dec(v___x_1596_);
lean_inc(v___x_1784_);
v___x_1785_ = l_Lean_Syntax_matchesNull(v___x_1784_, v___x_1595_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1784_);
v___x_1787_ = l_Lean_Syntax_matchesNull(v___x_1784_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec(v___x_1784_);
v___x_1788_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1789_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1792_, v_a_1584_, v_a_1585_);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = l_Lean_Syntax_getArg(v___x_1784_, v___x_1595_);
lean_dec(v___x_1784_);
v___x_1795_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1796_ = l_Lean_Syntax_isOfKind(v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1797_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1798_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1801_, v_a_1584_, v_a_1585_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v_stx_1583_);
v___x_1803_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1803_, 0, v___x_1588_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
return v___x_1805_;
}
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v___x_1784_);
lean_dec(v_stx_1583_);
v___x_1806_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1806_, 0, v___x_1604_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1809_);
lean_dec(v___x_1596_);
lean_inc(v___x_1810_);
v___x_1811_ = l_Lean_Syntax_matchesNull(v___x_1810_, v___x_1595_);
if (v___x_1811_ == 0)
{
uint8_t v___x_1812_; 
lean_inc(v___x_1810_);
v___x_1812_ = l_Lean_Syntax_matchesNull(v___x_1810_, v___x_1809_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec(v___x_1810_);
v___x_1813_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1814_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1817_, v_a_1584_, v_a_1585_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1819_ = l_Lean_Syntax_getArg(v___x_1810_, v___x_1595_);
lean_dec(v___x_1810_);
v___x_1820_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1821_ = l_Lean_Syntax_isOfKind(v___x_1819_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1822_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1823_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1826_, v_a_1584_, v_a_1585_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec(v_stx_1583_);
v___x_1828_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_1828_, 0, v___x_1588_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
}
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_dec(v___x_1810_);
lean_dec(v_stx_1583_);
v___x_1831_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_1831_, 0, v___x_1602_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec(v___x_1596_);
lean_dec(v_stx_1583_);
v___x_1834_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1836_ = lean_unsigned_to_nat(1u);
v___x_1837_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1836_);
lean_dec(v___x_1596_);
lean_inc(v___x_1837_);
v___x_1838_ = l_Lean_Syntax_matchesNull(v___x_1837_, v___x_1595_);
if (v___x_1838_ == 0)
{
uint8_t v___x_1839_; 
lean_inc(v___x_1837_);
v___x_1839_ = l_Lean_Syntax_matchesNull(v___x_1837_, v___x_1836_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec(v___x_1837_);
v___x_1840_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1841_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1844_, v_a_1584_, v_a_1585_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1846_ = l_Lean_Syntax_getArg(v___x_1837_, v___x_1595_);
lean_dec(v___x_1837_);
v___x_1847_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1848_ = l_Lean_Syntax_isOfKind(v___x_1846_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1849_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1850_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1853_, v_a_1584_, v_a_1585_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v_stx_1583_);
v___x_1855_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1855_, 0, v___x_1588_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_dec(v___x_1837_);
lean_dec(v_stx_1583_);
v___x_1858_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1858_, 0, v___x_1598_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_1861_);
lean_dec(v___x_1596_);
lean_inc(v___x_1862_);
v___x_1863_ = l_Lean_Syntax_matchesNull(v___x_1862_, v___x_1595_);
if (v___x_1863_ == 0)
{
uint8_t v___x_1864_; 
lean_inc(v___x_1862_);
v___x_1864_ = l_Lean_Syntax_matchesNull(v___x_1862_, v___x_1861_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_dec(v___x_1862_);
v___x_1865_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1866_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1869_, v_a_1584_, v_a_1585_);
return v___x_1870_;
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1871_ = l_Lean_Syntax_getArg(v___x_1862_, v___x_1595_);
lean_dec(v___x_1862_);
v___x_1872_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1873_ = l_Lean_Syntax_isOfKind(v___x_1871_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1874_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1875_ = l_Lean_MessageData_ofSyntax(v_stx_1583_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1878_, v_a_1584_, v_a_1585_);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v_stx_1583_);
v___x_1880_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1880_, 0, v___x_1588_);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec(v___x_1862_);
lean_dec(v_stx_1583_);
v___x_1883_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_1885_, v_a_1886_, v_a_1887_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_1890_, lean_object* v_msg_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1891_, v___y_1892_, v___y_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_1896_, lean_object* v_msg_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_1896_, v_msg_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_1902_, lean_object* v_ref_1903_, lean_object* v_msg_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_1903_, v_msg_1904_, v___y_1905_, v___y_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_1909_, lean_object* v_ref_1910_, lean_object* v_msg_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_1909_, v_ref_1910_, v_msg_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v_ref_1910_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1920_ = lean_unsigned_to_nat(1u);
v___x_1921_ = l_Lean_Syntax_getArg(v_stx_1916_, v___x_1920_);
v___x_1922_ = l_Lean_Syntax_isNone(v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = l_Lean_Syntax_getArg(v___x_1921_, v___x_1923_);
lean_dec(v___x_1921_);
v___x_1925_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_1924_, v_a_1917_, v_a_1918_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec(v___x_1921_);
v___x_1926_ = lean_box(3);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_1928_, v_a_1929_, v_a_1930_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_stx_1928_);
return v_res_1932_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_1935_ = l_Lean_stringToMessageData(v___x_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_1940_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1939_, v_a_1936_, v_a_1937_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_1941_, v_a_1942_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_1946_, v_a_1947_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_1955_, lean_object* v_b_1956_, uint8_t v_kind_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_toCold_1961_; lean_object* v_currNamespace_1962_; lean_object* v___x_1963_; lean_object* v_env_1964_; lean_object* v_nextMacroScope_1965_; lean_object* v_ngen_1966_; lean_object* v_auxDeclNGen_1967_; lean_object* v_traceState_1968_; lean_object* v_recordedDeps_1969_; lean_object* v_messages_1970_; lean_object* v_infoState_1971_; lean_object* v_snapshotTasks_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1984_; 
v_toCold_1961_ = lean_ctor_get(v___y_1958_, 0);
v_currNamespace_1962_ = lean_ctor_get(v_toCold_1961_, 4);
v___x_1963_ = lean_st_ref_take(v___y_1959_);
v_env_1964_ = lean_ctor_get(v___x_1963_, 0);
v_nextMacroScope_1965_ = lean_ctor_get(v___x_1963_, 1);
v_ngen_1966_ = lean_ctor_get(v___x_1963_, 2);
v_auxDeclNGen_1967_ = lean_ctor_get(v___x_1963_, 3);
v_traceState_1968_ = lean_ctor_get(v___x_1963_, 4);
v_recordedDeps_1969_ = lean_ctor_get(v___x_1963_, 6);
v_messages_1970_ = lean_ctor_get(v___x_1963_, 7);
v_infoState_1971_ = lean_ctor_get(v___x_1963_, 8);
v_snapshotTasks_1972_ = lean_ctor_get(v___x_1963_, 9);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v___x_1963_, 5);
lean_dec(v_unused_1985_);
v___x_1974_ = v___x_1963_;
v_isShared_1975_ = v_isSharedCheck_1984_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_snapshotTasks_1972_);
lean_inc(v_infoState_1971_);
lean_inc(v_messages_1970_);
lean_inc(v_recordedDeps_1969_);
lean_inc(v_traceState_1968_);
lean_inc(v_auxDeclNGen_1967_);
lean_inc(v_ngen_1966_);
lean_inc(v_nextMacroScope_1965_);
lean_inc(v_env_1964_);
lean_dec(v___x_1963_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1984_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1976_ = lean_box(0);
lean_inc(v_currNamespace_1962_);
v___x_1977_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1964_, v_ext_1955_, v_b_1956_, v_kind_1957_, v_currNamespace_1962_);
v___x_1978_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 5, v___x_1978_);
lean_ctor_set(v___x_1974_, 0, v___x_1977_);
v___x_1980_ = v___x_1974_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_nextMacroScope_1965_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_ngen_1966_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_auxDeclNGen_1967_);
lean_ctor_set(v_reuseFailAlloc_1983_, 4, v_traceState_1968_);
lean_ctor_set(v_reuseFailAlloc_1983_, 5, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1983_, 6, v_recordedDeps_1969_);
lean_ctor_set(v_reuseFailAlloc_1983_, 7, v_messages_1970_);
lean_ctor_set(v_reuseFailAlloc_1983_, 8, v_infoState_1971_);
lean_ctor_set(v_reuseFailAlloc_1983_, 9, v_snapshotTasks_1972_);
v___x_1980_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_st_ref_put(v___y_1959_, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1976_);
return v___x_1982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_1986_, lean_object* v_b_1987_, lean_object* v_kind_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
uint8_t v_kind_boxed_1992_; lean_object* v_res_1993_; 
v_kind_boxed_1992_ = lean_unbox(v_kind_1988_);
v_res_1993_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_1986_, v_b_1987_, v_kind_boxed_1992_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_1994_, lean_object* v_00_u03b2_1995_, lean_object* v_00_u03c3_1996_, lean_object* v_ext_1997_, lean_object* v_b_1998_, uint8_t v_kind_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_1997_, v_b_1998_, v_kind_1999_, v___y_2000_, v___y_2001_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_2004_, lean_object* v_00_u03b2_2005_, lean_object* v_00_u03c3_2006_, lean_object* v_ext_2007_, lean_object* v_b_2008_, lean_object* v_kind_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
uint8_t v_kind_boxed_2013_; lean_object* v_res_2014_; 
v_kind_boxed_2013_ = lean_unbox(v_kind_2009_);
v_res_2014_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_2004_, v_00_u03b2_2005_, v_00_u03c3_2006_, v_ext_2007_, v_b_2008_, v_kind_boxed_2013_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_2015_, lean_object* v_declName_2016_, uint8_t v_eager_2017_, uint8_t v_attrKind_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; 
lean_inc(v_declName_2016_);
v___x_2022_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_2016_, v_eager_2017_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_dec_ref_known(v___x_2022_, 1);
v___x_2023_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2023_, 0, v_declName_2016_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*1, v_eager_2017_);
v___x_2024_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2015_, v___x_2023_, v_attrKind_2018_, v_a_2019_, v_a_2020_);
return v___x_2024_;
}
else
{
lean_dec(v_declName_2016_);
lean_dec_ref(v_ext_2015_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_2025_, lean_object* v_declName_2026_, lean_object* v_eager_2027_, lean_object* v_attrKind_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
uint8_t v_eager_boxed_2032_; uint8_t v_attrKind_boxed_2033_; lean_object* v_res_2034_; 
v_eager_boxed_2032_ = lean_unbox(v_eager_2027_);
v_attrKind_boxed_2033_ = lean_unbox(v_attrKind_2028_);
v_res_2034_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2025_, v_declName_2026_, v_eager_boxed_2032_, v_attrKind_boxed_2033_, v_a_2029_, v_a_2030_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_2035_, lean_object* v_declName_2036_, uint8_t v_attrKind_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v___x_2041_; 
lean_inc(v_declName_2036_);
v___x_2041_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_2036_, v_a_2038_, v_a_2039_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2049_; 
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v___x_2041_, 0);
lean_dec(v_unused_2050_);
v___x_2043_ = v___x_2041_;
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v___x_2041_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v_declName_2036_);
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_declName_2036_);
v___x_2046_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2035_, v___x_2046_, v_attrKind_2037_, v_a_2038_, v_a_2039_);
return v___x_2047_;
}
}
}
else
{
lean_dec(v_declName_2036_);
lean_dec_ref(v_ext_2035_);
return v___x_2041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_2051_, lean_object* v_declName_2052_, lean_object* v_attrKind_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
uint8_t v_attrKind_boxed_2057_; lean_object* v_res_2058_; 
v_attrKind_boxed_2057_ = lean_unbox(v_attrKind_2053_);
v_res_2058_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2051_, v_declName_2052_, v_attrKind_boxed_2057_, v_a_2054_, v_a_2055_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_2059_, lean_object* v_declName_2060_, uint8_t v_attrKind_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_declName_2060_);
v___x_2066_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2059_, v___x_2065_, v_attrKind_2061_, v_a_2062_, v_a_2063_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_2067_, lean_object* v_declName_2068_, lean_object* v_attrKind_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
uint8_t v_attrKind_boxed_2073_; lean_object* v_res_2074_; 
v_attrKind_boxed_2073_ = lean_unbox(v_attrKind_2069_);
v_res_2074_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2067_, v_declName_2068_, v_attrKind_boxed_2073_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_2075_, lean_object* v_s_2076_){
_start:
{
lean_object* v_casesTypes_2077_; lean_object* v_funCC_2078_; lean_object* v_ematch_2079_; lean_object* v_inj_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_casesTypes_2077_ = lean_ctor_get(v_s_2076_, 0);
v_funCC_2078_ = lean_ctor_get(v_s_2076_, 2);
v_ematch_2079_ = lean_ctor_get(v_s_2076_, 3);
v_inj_2080_ = lean_ctor_get(v_s_2076_, 4);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_s_2076_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v_s_2076_, 1);
lean_dec(v_unused_2088_);
v___x_2082_ = v_s_2076_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_inj_2080_);
lean_inc(v_ematch_2079_);
lean_inc(v_funCC_2078_);
lean_inc(v_casesTypes_2077_);
lean_dec(v_s_2076_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 1, v_a_2075_);
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_casesTypes_2077_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_a_2075_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_funCC_2078_);
lean_ctor_set(v_reuseFailAlloc_2086_, 3, v_ematch_2079_);
lean_ctor_set(v_reuseFailAlloc_2086_, 4, v_inj_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_2089_, lean_object* v_declName_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v_ext_2096_; lean_object* v_toEnvExtension_2097_; lean_object* v_env_2098_; lean_object* v_asyncMode_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v_extThms_2102_; lean_object* v___x_2103_; 
v___x_2094_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2095_ = lean_st_ref_get(v_a_2092_);
v_ext_2096_ = lean_ctor_get(v_ext_2089_, 1);
v_toEnvExtension_2097_ = lean_ctor_get(v_ext_2096_, 0);
v_env_2098_ = lean_ctor_get(v___x_2095_, 0);
lean_inc_ref(v_env_2098_);
lean_dec(v___x_2095_);
v_asyncMode_2099_ = lean_ctor_get(v_toEnvExtension_2097_, 2);
v___x_2100_ = 0;
v___x_2101_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2094_, v_ext_2089_, v_env_2098_, v_asyncMode_2099_, v___x_2100_);
v_extThms_2102_ = lean_ctor_get(v___x_2101_, 1);
lean_inc_ref(v_extThms_2102_);
lean_dec(v___x_2101_);
v___x_2103_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_2102_, v_declName_2090_, v_a_2091_, v_a_2092_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2134_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2134_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2134_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___f_2108_; lean_object* v___x_2109_; lean_object* v_env_2110_; lean_object* v_nextMacroScope_2111_; lean_object* v_ngen_2112_; lean_object* v_auxDeclNGen_2113_; lean_object* v_traceState_2114_; lean_object* v_recordedDeps_2115_; lean_object* v_messages_2116_; lean_object* v_infoState_2117_; lean_object* v_snapshotTasks_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2132_; 
v___f_2108_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_2108_, 0, v_a_2104_);
v___x_2109_ = lean_st_ref_take(v_a_2092_);
v_env_2110_ = lean_ctor_get(v___x_2109_, 0);
v_nextMacroScope_2111_ = lean_ctor_get(v___x_2109_, 1);
v_ngen_2112_ = lean_ctor_get(v___x_2109_, 2);
v_auxDeclNGen_2113_ = lean_ctor_get(v___x_2109_, 3);
v_traceState_2114_ = lean_ctor_get(v___x_2109_, 4);
v_recordedDeps_2115_ = lean_ctor_get(v___x_2109_, 6);
v_messages_2116_ = lean_ctor_get(v___x_2109_, 7);
v_infoState_2117_ = lean_ctor_get(v___x_2109_, 8);
v_snapshotTasks_2118_ = lean_ctor_get(v___x_2109_, 9);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v___x_2109_, 5);
lean_dec(v_unused_2133_);
v___x_2120_ = v___x_2109_;
v_isShared_2121_ = v_isSharedCheck_2132_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_snapshotTasks_2118_);
lean_inc(v_infoState_2117_);
lean_inc(v_messages_2116_);
lean_inc(v_recordedDeps_2115_);
lean_inc(v_traceState_2114_);
lean_inc(v_auxDeclNGen_2113_);
lean_inc(v_ngen_2112_);
lean_inc(v_nextMacroScope_2111_);
lean_inc(v_env_2110_);
lean_dec(v___x_2109_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2132_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2122_ = lean_box(0);
v___x_2123_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2089_, v_env_2110_, v___f_2108_);
v___x_2124_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 5, v___x_2124_);
lean_ctor_set(v___x_2120_, 0, v___x_2123_);
v___x_2126_ = v___x_2120_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_nextMacroScope_2111_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_ngen_2112_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_auxDeclNGen_2113_);
lean_ctor_set(v_reuseFailAlloc_2131_, 4, v_traceState_2114_);
lean_ctor_set(v_reuseFailAlloc_2131_, 5, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2131_, 6, v_recordedDeps_2115_);
lean_ctor_set(v_reuseFailAlloc_2131_, 7, v_messages_2116_);
lean_ctor_set(v_reuseFailAlloc_2131_, 8, v_infoState_2117_);
lean_ctor_set(v_reuseFailAlloc_2131_, 9, v_snapshotTasks_2118_);
v___x_2126_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_st_ref_put(v_a_2092_, v___x_2126_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2122_);
v___x_2129_ = v___x_2106_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2122_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v_ext_2089_);
v_a_2135_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2103_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2103_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_2143_, lean_object* v_declName_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2143_, v_declName_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_2149_, lean_object* v_s_2150_){
_start:
{
lean_object* v_extThms_2151_; lean_object* v_funCC_2152_; lean_object* v_ematch_2153_; lean_object* v_inj_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
v_extThms_2151_ = lean_ctor_get(v_s_2150_, 1);
v_funCC_2152_ = lean_ctor_get(v_s_2150_, 2);
v_ematch_2153_ = lean_ctor_get(v_s_2150_, 3);
v_inj_2154_ = lean_ctor_get(v_s_2150_, 4);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_s_2150_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v_s_2150_, 0);
lean_dec(v_unused_2162_);
v___x_2156_ = v_s_2150_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_inj_2154_);
lean_inc(v_ematch_2153_);
lean_inc(v_funCC_2152_);
lean_inc(v_extThms_2151_);
lean_dec(v_s_2150_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v_a_2149_);
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2149_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_extThms_2151_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_funCC_2152_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v_ematch_2153_);
lean_ctor_set(v_reuseFailAlloc_2160_, 4, v_inj_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_2163_, lean_object* v_declName_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_inc(v_declName_2164_);
v___x_2169_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_2164_, v_a_2165_, v_a_2166_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v___x_2170_; lean_object* v_ext_2171_; lean_object* v_toEnvExtension_2172_; lean_object* v_env_2173_; lean_object* v_asyncMode_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v_casesTypes_2177_; lean_object* v___x_2178_; 
lean_dec_ref_known(v___x_2169_, 1);
v___x_2170_ = lean_st_ref_get(v_a_2166_);
v_ext_2171_ = lean_ctor_get(v_ext_2163_, 1);
v_toEnvExtension_2172_ = lean_ctor_get(v_ext_2171_, 0);
v_env_2173_ = lean_ctor_get(v___x_2170_, 0);
lean_inc_ref(v_env_2173_);
lean_dec(v___x_2170_);
v_asyncMode_2174_ = lean_ctor_get(v_toEnvExtension_2172_, 2);
v___x_2175_ = 0;
v___x_2176_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2168_, v_ext_2163_, v_env_2173_, v_asyncMode_2174_, v___x_2175_);
v_casesTypes_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc_ref(v_casesTypes_2177_);
lean_dec(v___x_2176_);
v___x_2178_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_2177_, v_declName_2164_, v_a_2165_, v_a_2166_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2209_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2209_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2209_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___f_2183_; lean_object* v___x_2184_; lean_object* v_env_2185_; lean_object* v_nextMacroScope_2186_; lean_object* v_ngen_2187_; lean_object* v_auxDeclNGen_2188_; lean_object* v_traceState_2189_; lean_object* v_recordedDeps_2190_; lean_object* v_messages_2191_; lean_object* v_infoState_2192_; lean_object* v_snapshotTasks_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2207_; 
v___f_2183_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_2183_, 0, v_a_2179_);
v___x_2184_ = lean_st_ref_take(v_a_2166_);
v_env_2185_ = lean_ctor_get(v___x_2184_, 0);
v_nextMacroScope_2186_ = lean_ctor_get(v___x_2184_, 1);
v_ngen_2187_ = lean_ctor_get(v___x_2184_, 2);
v_auxDeclNGen_2188_ = lean_ctor_get(v___x_2184_, 3);
v_traceState_2189_ = lean_ctor_get(v___x_2184_, 4);
v_recordedDeps_2190_ = lean_ctor_get(v___x_2184_, 6);
v_messages_2191_ = lean_ctor_get(v___x_2184_, 7);
v_infoState_2192_ = lean_ctor_get(v___x_2184_, 8);
v_snapshotTasks_2193_ = lean_ctor_get(v___x_2184_, 9);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; 
v_unused_2208_ = lean_ctor_get(v___x_2184_, 5);
lean_dec(v_unused_2208_);
v___x_2195_ = v___x_2184_;
v_isShared_2196_ = v_isSharedCheck_2207_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_snapshotTasks_2193_);
lean_inc(v_infoState_2192_);
lean_inc(v_messages_2191_);
lean_inc(v_recordedDeps_2190_);
lean_inc(v_traceState_2189_);
lean_inc(v_auxDeclNGen_2188_);
lean_inc(v_ngen_2187_);
lean_inc(v_nextMacroScope_2186_);
lean_inc(v_env_2185_);
lean_dec(v___x_2184_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2207_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2197_ = lean_box(0);
v___x_2198_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2163_, v_env_2185_, v___f_2183_);
v___x_2199_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 5, v___x_2199_);
lean_ctor_set(v___x_2195_, 0, v___x_2198_);
v___x_2201_ = v___x_2195_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_nextMacroScope_2186_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_ngen_2187_);
lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_auxDeclNGen_2188_);
lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_traceState_2189_);
lean_ctor_set(v_reuseFailAlloc_2206_, 5, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2206_, 6, v_recordedDeps_2190_);
lean_ctor_set(v_reuseFailAlloc_2206_, 7, v_messages_2191_);
lean_ctor_set(v_reuseFailAlloc_2206_, 8, v_infoState_2192_);
lean_ctor_set(v_reuseFailAlloc_2206_, 9, v_snapshotTasks_2193_);
v___x_2201_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2202_ = lean_st_ref_put(v_a_2166_, v___x_2201_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2197_);
v___x_2204_ = v___x_2181_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2197_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_ext_2163_);
v_a_2210_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2178_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2178_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_dec(v_declName_2164_);
lean_dec_ref(v_ext_2163_);
return v___x_2169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_2218_, lean_object* v_declName_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2218_, v_declName_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_2224_, lean_object* v_s_2225_){
_start:
{
lean_object* v_casesTypes_2226_; lean_object* v_extThms_2227_; lean_object* v_ematch_2228_; lean_object* v_inj_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
v_casesTypes_2226_ = lean_ctor_get(v_s_2225_, 0);
v_extThms_2227_ = lean_ctor_get(v_s_2225_, 1);
v_ematch_2228_ = lean_ctor_get(v_s_2225_, 3);
v_inj_2229_ = lean_ctor_get(v_s_2225_, 4);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_s_2225_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; 
v_unused_2237_ = lean_ctor_get(v_s_2225_, 2);
lean_dec(v_unused_2237_);
v___x_2231_ = v_s_2225_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_inj_2229_);
lean_inc(v_ematch_2228_);
lean_inc(v_extThms_2227_);
lean_inc(v_casesTypes_2226_);
lean_dec(v_s_2225_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 2, v___x_2224_);
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_casesTypes_2226_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_extThms_2227_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_ematch_2228_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_inj_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_2238_, lean_object* v_t_2239_){
_start:
{
if (lean_obj_tag(v_t_2239_) == 0)
{
lean_object* v_k_2240_; lean_object* v_v_2241_; lean_object* v_l_2242_; lean_object* v_r_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2897_; 
v_k_2240_ = lean_ctor_get(v_t_2239_, 1);
v_v_2241_ = lean_ctor_get(v_t_2239_, 2);
v_l_2242_ = lean_ctor_get(v_t_2239_, 3);
v_r_2243_ = lean_ctor_get(v_t_2239_, 4);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_t_2239_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v_t_2239_, 0);
lean_dec(v_unused_2898_);
v___x_2245_ = v_t_2239_;
v_isShared_2246_ = v_isSharedCheck_2897_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_r_2243_);
lean_inc(v_l_2242_);
lean_inc(v_v_2241_);
lean_inc(v_k_2240_);
lean_dec(v_t_2239_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2897_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
uint8_t v___x_2247_; 
v___x_2247_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2238_, v_k_2240_);
switch(v___x_2247_)
{
case 0:
{
lean_object* v_impl_2248_; lean_object* v___x_2249_; 
v_impl_2248_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2238_, v_l_2242_);
v___x_2249_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2248_) == 0)
{
if (lean_obj_tag(v_r_2243_) == 0)
{
lean_object* v_size_2250_; lean_object* v_size_2251_; lean_object* v_k_2252_; lean_object* v_v_2253_; lean_object* v_l_2254_; lean_object* v_r_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v_size_2250_ = lean_ctor_get(v_impl_2248_, 0);
v_size_2251_ = lean_ctor_get(v_r_2243_, 0);
v_k_2252_ = lean_ctor_get(v_r_2243_, 1);
v_v_2253_ = lean_ctor_get(v_r_2243_, 2);
v_l_2254_ = lean_ctor_get(v_r_2243_, 3);
lean_inc(v_l_2254_);
v_r_2255_ = lean_ctor_get(v_r_2243_, 4);
v___x_2256_ = lean_unsigned_to_nat(3u);
v___x_2257_ = lean_nat_mul(v___x_2256_, v_size_2250_);
v___x_2258_ = lean_nat_dec_lt(v___x_2257_, v_size_2251_);
lean_dec(v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
lean_dec(v_l_2254_);
v___x_2259_ = lean_nat_add(v___x_2249_, v_size_2250_);
v___x_2260_ = lean_nat_add(v___x_2259_, v_size_2251_);
lean_dec(v___x_2259_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 3, v_impl_2248_);
lean_ctor_set(v___x_2245_, 0, v___x_2260_);
v___x_2262_ = v___x_2245_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2263_, 3, v_impl_2248_);
lean_ctor_set(v_reuseFailAlloc_2263_, 4, v_r_2243_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
else
{
lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2327_; 
lean_inc(v_r_2255_);
lean_inc(v_v_2253_);
lean_inc(v_k_2252_);
lean_inc(v_size_2251_);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_r_2243_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; lean_object* v_unused_2329_; lean_object* v_unused_2330_; lean_object* v_unused_2331_; lean_object* v_unused_2332_; 
v_unused_2328_ = lean_ctor_get(v_r_2243_, 4);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v_r_2243_, 3);
lean_dec(v_unused_2329_);
v_unused_2330_ = lean_ctor_get(v_r_2243_, 2);
lean_dec(v_unused_2330_);
v_unused_2331_ = lean_ctor_get(v_r_2243_, 1);
lean_dec(v_unused_2331_);
v_unused_2332_ = lean_ctor_get(v_r_2243_, 0);
lean_dec(v_unused_2332_);
v___x_2265_ = v_r_2243_;
v_isShared_2266_ = v_isSharedCheck_2327_;
goto v_resetjp_2264_;
}
else
{
lean_dec(v_r_2243_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2327_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v_size_2267_; lean_object* v_k_2268_; lean_object* v_v_2269_; lean_object* v_l_2270_; lean_object* v_r_2271_; lean_object* v_size_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v_size_2267_ = lean_ctor_get(v_l_2254_, 0);
v_k_2268_ = lean_ctor_get(v_l_2254_, 1);
v_v_2269_ = lean_ctor_get(v_l_2254_, 2);
v_l_2270_ = lean_ctor_get(v_l_2254_, 3);
v_r_2271_ = lean_ctor_get(v_l_2254_, 4);
v_size_2272_ = lean_ctor_get(v_r_2255_, 0);
v___x_2273_ = lean_unsigned_to_nat(2u);
v___x_2274_ = lean_nat_mul(v___x_2273_, v_size_2272_);
v___x_2275_ = lean_nat_dec_lt(v_size_2267_, v___x_2274_);
lean_dec(v___x_2274_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2303_; 
lean_inc(v_r_2271_);
lean_inc(v_l_2270_);
lean_inc(v_v_2269_);
lean_inc(v_k_2268_);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_l_2254_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; lean_object* v_unused_2305_; lean_object* v_unused_2306_; lean_object* v_unused_2307_; lean_object* v_unused_2308_; 
v_unused_2304_ = lean_ctor_get(v_l_2254_, 4);
lean_dec(v_unused_2304_);
v_unused_2305_ = lean_ctor_get(v_l_2254_, 3);
lean_dec(v_unused_2305_);
v_unused_2306_ = lean_ctor_get(v_l_2254_, 2);
lean_dec(v_unused_2306_);
v_unused_2307_ = lean_ctor_get(v_l_2254_, 1);
lean_dec(v_unused_2307_);
v_unused_2308_ = lean_ctor_get(v_l_2254_, 0);
lean_dec(v_unused_2308_);
v___x_2277_ = v_l_2254_;
v_isShared_2278_ = v_isSharedCheck_2303_;
goto v_resetjp_2276_;
}
else
{
lean_dec(v_l_2254_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2303_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2293_; 
v___x_2279_ = lean_nat_add(v___x_2249_, v_size_2250_);
v___x_2280_ = lean_nat_add(v___x_2279_, v_size_2251_);
lean_dec(v_size_2251_);
if (lean_obj_tag(v_l_2270_) == 0)
{
lean_object* v_size_2301_; 
v_size_2301_ = lean_ctor_get(v_l_2270_, 0);
lean_inc(v_size_2301_);
v___y_2293_ = v_size_2301_;
goto v___jp_2292_;
}
else
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_unsigned_to_nat(0u);
v___y_2293_ = v___x_2302_;
goto v___jp_2292_;
}
v___jp_2281_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_nat_add(v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec(v___y_2283_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 4, v_r_2255_);
lean_ctor_set(v___x_2277_, 3, v_r_2271_);
lean_ctor_set(v___x_2277_, 2, v_v_2253_);
lean_ctor_set(v___x_2277_, 1, v_k_2252_);
lean_ctor_set(v___x_2277_, 0, v___x_2285_);
v___x_2287_ = v___x_2277_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_k_2252_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v_v_2253_);
lean_ctor_set(v_reuseFailAlloc_2291_, 3, v_r_2271_);
lean_ctor_set(v_reuseFailAlloc_2291_, 4, v_r_2255_);
v___x_2287_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2289_; 
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 4, v___x_2287_);
lean_ctor_set(v___x_2265_, 3, v___y_2282_);
lean_ctor_set(v___x_2265_, 2, v_v_2269_);
lean_ctor_set(v___x_2265_, 1, v_k_2268_);
lean_ctor_set(v___x_2265_, 0, v___x_2280_);
v___x_2289_ = v___x_2265_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_k_2268_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_v_2269_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v___y_2282_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
v___jp_2292_:
{
lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2294_ = lean_nat_add(v___x_2279_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec(v___x_2279_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v_l_2270_);
lean_ctor_set(v___x_2245_, 3, v_impl_2248_);
lean_ctor_set(v___x_2245_, 0, v___x_2294_);
v___x_2296_ = v___x_2245_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_impl_2248_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_l_2270_);
v___x_2296_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_nat_add(v___x_2249_, v_size_2272_);
if (lean_obj_tag(v_r_2271_) == 0)
{
lean_object* v_size_2298_; 
v_size_2298_ = lean_ctor_get(v_r_2271_, 0);
lean_inc(v_size_2298_);
v___y_2282_ = v___x_2296_;
v___y_2283_ = v___x_2297_;
v___y_2284_ = v_size_2298_;
goto v___jp_2281_;
}
else
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_unsigned_to_nat(0u);
v___y_2282_ = v___x_2296_;
v___y_2283_ = v___x_2297_;
v___y_2284_ = v___x_2299_;
goto v___jp_2281_;
}
}
}
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
lean_del_object(v___x_2245_);
v___x_2309_ = lean_nat_add(v___x_2249_, v_size_2250_);
v___x_2310_ = lean_nat_add(v___x_2309_, v_size_2251_);
lean_dec(v_size_2251_);
v___x_2311_ = lean_nat_add(v___x_2309_, v_size_2267_);
lean_dec(v___x_2309_);
lean_inc_ref(v_impl_2248_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 4, v_l_2254_);
lean_ctor_set(v___x_2265_, 3, v_impl_2248_);
lean_ctor_set(v___x_2265_, 2, v_v_2241_);
lean_ctor_set(v___x_2265_, 1, v_k_2240_);
lean_ctor_set(v___x_2265_, 0, v___x_2311_);
v___x_2313_ = v___x_2265_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2326_, 3, v_impl_2248_);
lean_ctor_set(v_reuseFailAlloc_2326_, 4, v_l_2254_);
v___x_2313_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_isSharedCheck_2320_ = !lean_is_exclusive(v_impl_2248_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; lean_object* v_unused_2322_; lean_object* v_unused_2323_; lean_object* v_unused_2324_; lean_object* v_unused_2325_; 
v_unused_2321_ = lean_ctor_get(v_impl_2248_, 4);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_impl_2248_, 3);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_impl_2248_, 2);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_impl_2248_, 1);
lean_dec(v_unused_2324_);
v_unused_2325_ = lean_ctor_get(v_impl_2248_, 0);
lean_dec(v_unused_2325_);
v___x_2315_ = v_impl_2248_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_dec(v_impl_2248_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v_r_2255_);
lean_ctor_set(v___x_2315_, 3, v___x_2313_);
lean_ctor_set(v___x_2315_, 2, v_v_2253_);
lean_ctor_set(v___x_2315_, 1, v_k_2252_);
lean_ctor_set(v___x_2315_, 0, v___x_2310_);
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_k_2252_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_v_2253_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_r_2255_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v_size_2333_ = lean_ctor_get(v_impl_2248_, 0);
v___x_2334_ = lean_nat_add(v___x_2249_, v_size_2333_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 3, v_impl_2248_);
lean_ctor_set(v___x_2245_, 0, v___x_2334_);
v___x_2336_ = v___x_2245_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_impl_2248_);
lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_r_2243_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
else
{
if (lean_obj_tag(v_r_2243_) == 0)
{
lean_object* v_l_2338_; 
v_l_2338_ = lean_ctor_get(v_r_2243_, 3);
lean_inc(v_l_2338_);
if (lean_obj_tag(v_l_2338_) == 0)
{
lean_object* v_r_2339_; 
v_r_2339_ = lean_ctor_get(v_r_2243_, 4);
lean_inc(v_r_2339_);
if (lean_obj_tag(v_r_2339_) == 0)
{
lean_object* v_size_2340_; lean_object* v_k_2341_; lean_object* v_v_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2355_; 
v_size_2340_ = lean_ctor_get(v_r_2243_, 0);
v_k_2341_ = lean_ctor_get(v_r_2243_, 1);
v_v_2342_ = lean_ctor_get(v_r_2243_, 2);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_r_2243_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; lean_object* v_unused_2357_; 
v_unused_2356_ = lean_ctor_get(v_r_2243_, 4);
lean_dec(v_unused_2356_);
v_unused_2357_ = lean_ctor_get(v_r_2243_, 3);
lean_dec(v_unused_2357_);
v___x_2344_ = v_r_2243_;
v_isShared_2345_ = v_isSharedCheck_2355_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_v_2342_);
lean_inc(v_k_2341_);
lean_inc(v_size_2340_);
lean_dec(v_r_2243_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2355_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_size_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v_size_2346_ = lean_ctor_get(v_l_2338_, 0);
v___x_2347_ = lean_nat_add(v___x_2249_, v_size_2340_);
lean_dec(v_size_2340_);
v___x_2348_ = lean_nat_add(v___x_2249_, v_size_2346_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 4, v_l_2338_);
lean_ctor_set(v___x_2344_, 3, v_impl_2248_);
lean_ctor_set(v___x_2344_, 2, v_v_2241_);
lean_ctor_set(v___x_2344_, 1, v_k_2240_);
lean_ctor_set(v___x_2344_, 0, v___x_2348_);
v___x_2350_ = v___x_2344_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2354_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2354_, 3, v_impl_2248_);
lean_ctor_set(v_reuseFailAlloc_2354_, 4, v_l_2338_);
v___x_2350_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2352_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v_r_2339_);
lean_ctor_set(v___x_2245_, 3, v___x_2350_);
lean_ctor_set(v___x_2245_, 2, v_v_2342_);
lean_ctor_set(v___x_2245_, 1, v_k_2341_);
lean_ctor_set(v___x_2245_, 0, v___x_2347_);
v___x_2352_ = v___x_2245_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_k_2341_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v_v_2342_);
lean_ctor_set(v_reuseFailAlloc_2353_, 3, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2353_, 4, v_r_2339_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v_k_2358_; lean_object* v_v_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2382_; 
v_k_2358_ = lean_ctor_get(v_r_2243_, 1);
v_v_2359_ = lean_ctor_get(v_r_2243_, 2);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_r_2243_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; lean_object* v_unused_2384_; lean_object* v_unused_2385_; 
v_unused_2383_ = lean_ctor_get(v_r_2243_, 4);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_r_2243_, 3);
lean_dec(v_unused_2384_);
v_unused_2385_ = lean_ctor_get(v_r_2243_, 0);
lean_dec(v_unused_2385_);
v___x_2361_ = v_r_2243_;
v_isShared_2362_ = v_isSharedCheck_2382_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_v_2359_);
lean_inc(v_k_2358_);
lean_dec(v_r_2243_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2382_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_k_2363_; lean_object* v_v_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2378_; 
v_k_2363_ = lean_ctor_get(v_l_2338_, 1);
v_v_2364_ = lean_ctor_get(v_l_2338_, 2);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_l_2338_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; lean_object* v_unused_2380_; lean_object* v_unused_2381_; 
v_unused_2379_ = lean_ctor_get(v_l_2338_, 4);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_l_2338_, 3);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_l_2338_, 0);
lean_dec(v_unused_2381_);
v___x_2366_ = v_l_2338_;
v_isShared_2367_ = v_isSharedCheck_2378_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_v_2364_);
lean_inc(v_k_2363_);
lean_dec(v_l_2338_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2378_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2368_ = lean_unsigned_to_nat(3u);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 4, v_r_2339_);
lean_ctor_set(v___x_2366_, 3, v_r_2339_);
lean_ctor_set(v___x_2366_, 2, v_v_2241_);
lean_ctor_set(v___x_2366_, 1, v_k_2240_);
lean_ctor_set(v___x_2366_, 0, v___x_2249_);
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2377_, 3, v_r_2339_);
lean_ctor_set(v_reuseFailAlloc_2377_, 4, v_r_2339_);
v___x_2370_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 3, v_r_2339_);
lean_ctor_set(v___x_2361_, 0, v___x_2249_);
v___x_2372_ = v___x_2361_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_k_2358_);
lean_ctor_set(v_reuseFailAlloc_2376_, 2, v_v_2359_);
lean_ctor_set(v_reuseFailAlloc_2376_, 3, v_r_2339_);
lean_ctor_set(v_reuseFailAlloc_2376_, 4, v_r_2339_);
v___x_2372_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v___x_2372_);
lean_ctor_set(v___x_2245_, 3, v___x_2370_);
lean_ctor_set(v___x_2245_, 2, v_v_2364_);
lean_ctor_set(v___x_2245_, 1, v_k_2363_);
lean_ctor_set(v___x_2245_, 0, v___x_2368_);
v___x_2374_ = v___x_2245_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_k_2363_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_v_2364_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2386_; 
v_r_2386_ = lean_ctor_get(v_r_2243_, 4);
lean_inc(v_r_2386_);
if (lean_obj_tag(v_r_2386_) == 0)
{
lean_object* v_k_2387_; lean_object* v_v_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2399_; 
v_k_2387_ = lean_ctor_get(v_r_2243_, 1);
v_v_2388_ = lean_ctor_get(v_r_2243_, 2);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_r_2243_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; lean_object* v_unused_2401_; lean_object* v_unused_2402_; 
v_unused_2400_ = lean_ctor_get(v_r_2243_, 4);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_r_2243_, 3);
lean_dec(v_unused_2401_);
v_unused_2402_ = lean_ctor_get(v_r_2243_, 0);
lean_dec(v_unused_2402_);
v___x_2390_ = v_r_2243_;
v_isShared_2391_ = v_isSharedCheck_2399_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_v_2388_);
lean_inc(v_k_2387_);
lean_dec(v_r_2243_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2399_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = lean_unsigned_to_nat(3u);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 4, v_l_2338_);
lean_ctor_set(v___x_2390_, 2, v_v_2241_);
lean_ctor_set(v___x_2390_, 1, v_k_2240_);
lean_ctor_set(v___x_2390_, 0, v___x_2249_);
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_l_2338_);
lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_l_2338_);
v___x_2394_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2396_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v_r_2386_);
lean_ctor_set(v___x_2245_, 3, v___x_2394_);
lean_ctor_set(v___x_2245_, 2, v_v_2388_);
lean_ctor_set(v___x_2245_, 1, v_k_2387_);
lean_ctor_set(v___x_2245_, 0, v___x_2392_);
v___x_2396_ = v___x_2245_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_k_2387_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_v_2388_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_r_2386_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_object* v_size_2403_; lean_object* v_k_2404_; lean_object* v_v_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2416_; 
v_size_2403_ = lean_ctor_get(v_r_2243_, 0);
v_k_2404_ = lean_ctor_get(v_r_2243_, 1);
v_v_2405_ = lean_ctor_get(v_r_2243_, 2);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_r_2243_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; lean_object* v_unused_2418_; 
v_unused_2417_ = lean_ctor_get(v_r_2243_, 4);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_r_2243_, 3);
lean_dec(v_unused_2418_);
v___x_2407_ = v_r_2243_;
v_isShared_2408_ = v_isSharedCheck_2416_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_v_2405_);
lean_inc(v_k_2404_);
lean_inc(v_size_2403_);
lean_dec(v_r_2243_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2416_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 3, v_r_2386_);
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_size_2403_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_k_2404_);
lean_ctor_set(v_reuseFailAlloc_2415_, 2, v_v_2405_);
lean_ctor_set(v_reuseFailAlloc_2415_, 3, v_r_2386_);
lean_ctor_set(v_reuseFailAlloc_2415_, 4, v_r_2386_);
v___x_2410_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2411_ = lean_unsigned_to_nat(2u);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v___x_2410_);
lean_ctor_set(v___x_2245_, 3, v_r_2386_);
lean_ctor_set(v___x_2245_, 0, v___x_2411_);
v___x_2413_ = v___x_2245_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2414_, 3, v_r_2386_);
lean_ctor_set(v_reuseFailAlloc_2414_, 4, v___x_2410_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
}
else
{
lean_object* v___x_2420_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 3, v_r_2243_);
lean_ctor_set(v___x_2245_, 0, v___x_2249_);
v___x_2420_ = v___x_2245_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2421_, 3, v_r_2243_);
lean_ctor_set(v_reuseFailAlloc_2421_, 4, v_r_2243_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2245_);
lean_dec(v_v_2241_);
lean_dec(v_k_2240_);
if (lean_obj_tag(v_l_2242_) == 0)
{
if (lean_obj_tag(v_r_2243_) == 0)
{
lean_object* v_size_2422_; lean_object* v_k_2423_; lean_object* v_v_2424_; lean_object* v_l_2425_; lean_object* v_r_2426_; lean_object* v_size_2427_; lean_object* v_k_2428_; lean_object* v_v_2429_; lean_object* v_l_2430_; lean_object* v_r_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v_size_2422_ = lean_ctor_get(v_l_2242_, 0);
v_k_2423_ = lean_ctor_get(v_l_2242_, 1);
v_v_2424_ = lean_ctor_get(v_l_2242_, 2);
v_l_2425_ = lean_ctor_get(v_l_2242_, 3);
v_r_2426_ = lean_ctor_get(v_l_2242_, 4);
lean_inc(v_r_2426_);
v_size_2427_ = lean_ctor_get(v_r_2243_, 0);
v_k_2428_ = lean_ctor_get(v_r_2243_, 1);
v_v_2429_ = lean_ctor_get(v_r_2243_, 2);
v_l_2430_ = lean_ctor_get(v_r_2243_, 3);
lean_inc(v_l_2430_);
v_r_2431_ = lean_ctor_get(v_r_2243_, 4);
v___x_2432_ = lean_unsigned_to_nat(1u);
v___x_2433_ = lean_nat_dec_lt(v_size_2422_, v_size_2427_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2569_; 
lean_inc(v_l_2425_);
lean_inc(v_v_2424_);
lean_inc(v_k_2423_);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_l_2242_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; lean_object* v_unused_2571_; lean_object* v_unused_2572_; lean_object* v_unused_2573_; lean_object* v_unused_2574_; 
v_unused_2570_ = lean_ctor_get(v_l_2242_, 4);
lean_dec(v_unused_2570_);
v_unused_2571_ = lean_ctor_get(v_l_2242_, 3);
lean_dec(v_unused_2571_);
v_unused_2572_ = lean_ctor_get(v_l_2242_, 2);
lean_dec(v_unused_2572_);
v_unused_2573_ = lean_ctor_get(v_l_2242_, 1);
lean_dec(v_unused_2573_);
v_unused_2574_ = lean_ctor_get(v_l_2242_, 0);
lean_dec(v_unused_2574_);
v___x_2435_ = v_l_2242_;
v_isShared_2436_ = v_isSharedCheck_2569_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v_l_2242_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2569_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v_tree_2438_; 
v___x_2437_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2423_, v_v_2424_, v_l_2425_, v_r_2426_);
v_tree_2438_ = lean_ctor_get(v___x_2437_, 2);
if (lean_obj_tag(v_tree_2438_) == 0)
{
lean_object* v_k_2439_; lean_object* v_v_2440_; lean_object* v_size_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
lean_inc_ref(v_tree_2438_);
v_k_2439_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_k_2439_);
v_v_2440_ = lean_ctor_get(v___x_2437_, 1);
lean_inc(v_v_2440_);
lean_dec_ref(v___x_2437_);
v_size_2441_ = lean_ctor_get(v_tree_2438_, 0);
v___x_2442_ = lean_unsigned_to_nat(3u);
v___x_2443_ = lean_nat_mul(v___x_2442_, v_size_2441_);
v___x_2444_ = lean_nat_dec_lt(v___x_2443_, v_size_2427_);
lean_dec(v___x_2443_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
lean_dec(v_l_2430_);
v___x_2445_ = lean_nat_add(v___x_2432_, v_size_2441_);
v___x_2446_ = lean_nat_add(v___x_2445_, v_size_2427_);
lean_dec(v___x_2445_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v_r_2243_);
lean_ctor_set(v___x_2435_, 3, v_tree_2438_);
lean_ctor_set(v___x_2435_, 2, v_v_2440_);
lean_ctor_set(v___x_2435_, 1, v_k_2439_);
lean_ctor_set(v___x_2435_, 0, v___x_2446_);
v___x_2448_ = v___x_2435_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v_tree_2438_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v_r_2243_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
else
{
lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2504_; 
lean_inc(v_r_2431_);
lean_inc(v_v_2429_);
lean_inc(v_k_2428_);
lean_inc(v_size_2427_);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_r_2243_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; lean_object* v_unused_2506_; lean_object* v_unused_2507_; lean_object* v_unused_2508_; lean_object* v_unused_2509_; 
v_unused_2505_ = lean_ctor_get(v_r_2243_, 4);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_r_2243_, 3);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v_r_2243_, 2);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v_r_2243_, 1);
lean_dec(v_unused_2508_);
v_unused_2509_ = lean_ctor_get(v_r_2243_, 0);
lean_dec(v_unused_2509_);
v___x_2451_ = v_r_2243_;
v_isShared_2452_ = v_isSharedCheck_2504_;
goto v_resetjp_2450_;
}
else
{
lean_dec(v_r_2243_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2504_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_size_2453_; lean_object* v_k_2454_; lean_object* v_v_2455_; lean_object* v_l_2456_; lean_object* v_r_2457_; lean_object* v_size_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v_size_2453_ = lean_ctor_get(v_l_2430_, 0);
v_k_2454_ = lean_ctor_get(v_l_2430_, 1);
v_v_2455_ = lean_ctor_get(v_l_2430_, 2);
v_l_2456_ = lean_ctor_get(v_l_2430_, 3);
v_r_2457_ = lean_ctor_get(v_l_2430_, 4);
v_size_2458_ = lean_ctor_get(v_r_2431_, 0);
v___x_2459_ = lean_unsigned_to_nat(2u);
v___x_2460_ = lean_nat_mul(v___x_2459_, v_size_2458_);
v___x_2461_ = lean_nat_dec_lt(v_size_2453_, v___x_2460_);
lean_dec(v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2489_; 
lean_inc(v_r_2457_);
lean_inc(v_l_2456_);
lean_inc(v_v_2455_);
lean_inc(v_k_2454_);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_l_2430_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; lean_object* v_unused_2491_; lean_object* v_unused_2492_; lean_object* v_unused_2493_; lean_object* v_unused_2494_; 
v_unused_2490_ = lean_ctor_get(v_l_2430_, 4);
lean_dec(v_unused_2490_);
v_unused_2491_ = lean_ctor_get(v_l_2430_, 3);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_l_2430_, 2);
lean_dec(v_unused_2492_);
v_unused_2493_ = lean_ctor_get(v_l_2430_, 1);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v_l_2430_, 0);
lean_dec(v_unused_2494_);
v___x_2463_ = v_l_2430_;
v_isShared_2464_ = v_isSharedCheck_2489_;
goto v_resetjp_2462_;
}
else
{
lean_dec(v_l_2430_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2489_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2479_; 
v___x_2465_ = lean_nat_add(v___x_2432_, v_size_2441_);
v___x_2466_ = lean_nat_add(v___x_2465_, v_size_2427_);
lean_dec(v_size_2427_);
if (lean_obj_tag(v_l_2456_) == 0)
{
lean_object* v_size_2487_; 
v_size_2487_ = lean_ctor_get(v_l_2456_, 0);
lean_inc(v_size_2487_);
v___y_2479_ = v_size_2487_;
goto v___jp_2478_;
}
else
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_unsigned_to_nat(0u);
v___y_2479_ = v___x_2488_;
goto v___jp_2478_;
}
v___jp_2467_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = lean_nat_add(v___y_2468_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec(v___y_2468_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v_r_2431_);
lean_ctor_set(v___x_2463_, 3, v_r_2457_);
lean_ctor_set(v___x_2463_, 2, v_v_2429_);
lean_ctor_set(v___x_2463_, 1, v_k_2428_);
lean_ctor_set(v___x_2463_, 0, v___x_2471_);
v___x_2473_ = v___x_2463_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_r_2457_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_r_2431_);
v___x_2473_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2475_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v___x_2473_);
lean_ctor_set(v___x_2451_, 3, v___y_2469_);
lean_ctor_set(v___x_2451_, 2, v_v_2455_);
lean_ctor_set(v___x_2451_, 1, v_k_2454_);
lean_ctor_set(v___x_2451_, 0, v___x_2466_);
v___x_2475_ = v___x_2451_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v___y_2469_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v___x_2473_);
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
lean_object* v___x_2480_; lean_object* v___x_2482_; 
v___x_2480_ = lean_nat_add(v___x_2465_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec(v___x_2465_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v_l_2456_);
lean_ctor_set(v___x_2435_, 3, v_tree_2438_);
lean_ctor_set(v___x_2435_, 2, v_v_2440_);
lean_ctor_set(v___x_2435_, 1, v_k_2439_);
lean_ctor_set(v___x_2435_, 0, v___x_2480_);
v___x_2482_ = v___x_2435_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2486_, 3, v_tree_2438_);
lean_ctor_set(v_reuseFailAlloc_2486_, 4, v_l_2456_);
v___x_2482_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_nat_add(v___x_2432_, v_size_2458_);
if (lean_obj_tag(v_r_2457_) == 0)
{
lean_object* v_size_2484_; 
v_size_2484_ = lean_ctor_get(v_r_2457_, 0);
lean_inc(v_size_2484_);
v___y_2468_ = v___x_2483_;
v___y_2469_ = v___x_2482_;
v___y_2470_ = v_size_2484_;
goto v___jp_2467_;
}
else
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_unsigned_to_nat(0u);
v___y_2468_ = v___x_2483_;
v___y_2469_ = v___x_2482_;
v___y_2470_ = v___x_2485_;
goto v___jp_2467_;
}
}
}
}
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2495_ = lean_nat_add(v___x_2432_, v_size_2441_);
v___x_2496_ = lean_nat_add(v___x_2495_, v_size_2427_);
lean_dec(v_size_2427_);
v___x_2497_ = lean_nat_add(v___x_2495_, v_size_2453_);
lean_dec(v___x_2495_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v_l_2430_);
lean_ctor_set(v___x_2451_, 3, v_tree_2438_);
lean_ctor_set(v___x_2451_, 2, v_v_2440_);
lean_ctor_set(v___x_2451_, 1, v_k_2439_);
lean_ctor_set(v___x_2451_, 0, v___x_2497_);
v___x_2499_ = v___x_2451_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2503_, 3, v_tree_2438_);
lean_ctor_set(v_reuseFailAlloc_2503_, 4, v_l_2430_);
v___x_2499_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2501_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v_r_2431_);
lean_ctor_set(v___x_2435_, 3, v___x_2499_);
lean_ctor_set(v___x_2435_, 2, v_v_2429_);
lean_ctor_set(v___x_2435_, 1, v_k_2428_);
lean_ctor_set(v___x_2435_, 0, v___x_2496_);
v___x_2501_ = v___x_2435_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v_r_2431_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
}
else
{
lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2563_; 
lean_inc(v_r_2431_);
lean_inc(v_v_2429_);
lean_inc(v_k_2428_);
lean_inc(v_size_2427_);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_r_2243_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; lean_object* v_unused_2565_; lean_object* v_unused_2566_; lean_object* v_unused_2567_; lean_object* v_unused_2568_; 
v_unused_2564_ = lean_ctor_get(v_r_2243_, 4);
lean_dec(v_unused_2564_);
v_unused_2565_ = lean_ctor_get(v_r_2243_, 3);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_r_2243_, 2);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_r_2243_, 1);
lean_dec(v_unused_2567_);
v_unused_2568_ = lean_ctor_get(v_r_2243_, 0);
lean_dec(v_unused_2568_);
v___x_2511_ = v_r_2243_;
v_isShared_2512_ = v_isSharedCheck_2563_;
goto v_resetjp_2510_;
}
else
{
lean_dec(v_r_2243_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2563_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
if (lean_obj_tag(v_l_2430_) == 0)
{
if (lean_obj_tag(v_r_2431_) == 0)
{
lean_object* v_k_2513_; lean_object* v_v_2514_; lean_object* v_size_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
lean_inc(v_tree_2438_);
v_k_2513_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_k_2513_);
v_v_2514_ = lean_ctor_get(v___x_2437_, 1);
lean_inc(v_v_2514_);
lean_dec_ref(v___x_2437_);
v_size_2515_ = lean_ctor_get(v_l_2430_, 0);
v___x_2516_ = lean_nat_add(v___x_2432_, v_size_2427_);
lean_dec(v_size_2427_);
v___x_2517_ = lean_nat_add(v___x_2432_, v_size_2515_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 4, v_l_2430_);
lean_ctor_set(v___x_2511_, 3, v_tree_2438_);
lean_ctor_set(v___x_2511_, 2, v_v_2514_);
lean_ctor_set(v___x_2511_, 1, v_k_2513_);
lean_ctor_set(v___x_2511_, 0, v___x_2517_);
v___x_2519_ = v___x_2511_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_k_2513_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_v_2514_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v_tree_2438_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_l_2430_);
v___x_2519_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2521_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v_r_2431_);
lean_ctor_set(v___x_2435_, 3, v___x_2519_);
lean_ctor_set(v___x_2435_, 2, v_v_2429_);
lean_ctor_set(v___x_2435_, 1, v_k_2428_);
lean_ctor_set(v___x_2435_, 0, v___x_2516_);
v___x_2521_ = v___x_2435_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_r_2431_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
else
{
lean_object* v_k_2524_; lean_object* v_v_2525_; lean_object* v_k_2526_; lean_object* v_v_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v_size_2427_);
v_k_2524_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_k_2524_);
v_v_2525_ = lean_ctor_get(v___x_2437_, 1);
lean_inc(v_v_2525_);
lean_dec_ref(v___x_2437_);
v_k_2526_ = lean_ctor_get(v_l_2430_, 1);
v_v_2527_ = lean_ctor_get(v_l_2430_, 2);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_l_2430_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; lean_object* v_unused_2543_; lean_object* v_unused_2544_; 
v_unused_2542_ = lean_ctor_get(v_l_2430_, 4);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_l_2430_, 3);
lean_dec(v_unused_2543_);
v_unused_2544_ = lean_ctor_get(v_l_2430_, 0);
lean_dec(v_unused_2544_);
v___x_2529_ = v_l_2430_;
v_isShared_2530_ = v_isSharedCheck_2541_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_v_2527_);
lean_inc(v_k_2526_);
lean_dec(v_l_2430_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2541_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2531_ = lean_unsigned_to_nat(3u);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 4, v_r_2431_);
lean_ctor_set(v___x_2529_, 3, v_r_2431_);
lean_ctor_set(v___x_2529_, 2, v_v_2525_);
lean_ctor_set(v___x_2529_, 1, v_k_2524_);
lean_ctor_set(v___x_2529_, 0, v___x_2432_);
v___x_2533_ = v___x_2529_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_k_2524_);
lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_v_2525_);
lean_ctor_set(v_reuseFailAlloc_2540_, 3, v_r_2431_);
lean_ctor_set(v_reuseFailAlloc_2540_, 4, v_r_2431_);
v___x_2533_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2535_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 3, v_r_2431_);
lean_ctor_set(v___x_2511_, 0, v___x_2432_);
v___x_2535_ = v___x_2511_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_r_2431_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v_r_2431_);
v___x_2535_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2537_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v___x_2535_);
lean_ctor_set(v___x_2435_, 3, v___x_2533_);
lean_ctor_set(v___x_2435_, 2, v_v_2527_);
lean_ctor_set(v___x_2435_, 1, v_k_2526_);
lean_ctor_set(v___x_2435_, 0, v___x_2531_);
v___x_2537_ = v___x_2435_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_k_2526_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_v_2527_);
lean_ctor_set(v_reuseFailAlloc_2538_, 3, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2538_, 4, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2431_) == 0)
{
lean_object* v_k_2545_; lean_object* v_v_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_dec(v_size_2427_);
v_k_2545_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_k_2545_);
v_v_2546_ = lean_ctor_get(v___x_2437_, 1);
lean_inc(v_v_2546_);
lean_dec_ref(v___x_2437_);
v___x_2547_ = lean_unsigned_to_nat(3u);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 4, v_l_2430_);
lean_ctor_set(v___x_2511_, 2, v_v_2546_);
lean_ctor_set(v___x_2511_, 1, v_k_2545_);
lean_ctor_set(v___x_2511_, 0, v___x_2432_);
v___x_2549_ = v___x_2511_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_k_2545_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_v_2546_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_l_2430_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_l_2430_);
v___x_2549_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2551_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v_r_2431_);
lean_ctor_set(v___x_2435_, 3, v___x_2549_);
lean_ctor_set(v___x_2435_, 2, v_v_2429_);
lean_ctor_set(v___x_2435_, 1, v_k_2428_);
lean_ctor_set(v___x_2435_, 0, v___x_2547_);
v___x_2551_ = v___x_2435_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_r_2431_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
else
{
lean_object* v_k_2554_; lean_object* v_v_2555_; lean_object* v___x_2557_; 
v_k_2554_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_k_2554_);
v_v_2555_ = lean_ctor_get(v___x_2437_, 1);
lean_inc(v_v_2555_);
lean_dec_ref(v___x_2437_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 3, v_r_2431_);
v___x_2557_ = v___x_2511_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_size_2427_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_r_2431_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_r_2431_);
v___x_2557_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2558_ = lean_unsigned_to_nat(2u);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v___x_2557_);
lean_ctor_set(v___x_2435_, 3, v_r_2431_);
lean_ctor_set(v___x_2435_, 2, v_v_2555_);
lean_ctor_set(v___x_2435_, 1, v_k_2554_);
lean_ctor_set(v___x_2435_, 0, v___x_2558_);
v___x_2560_ = v___x_2435_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_k_2554_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_v_2555_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_r_2431_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v___x_2557_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
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
lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2727_; 
lean_inc(v_r_2431_);
lean_inc(v_v_2429_);
lean_inc(v_k_2428_);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_r_2243_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; lean_object* v_unused_2729_; lean_object* v_unused_2730_; lean_object* v_unused_2731_; lean_object* v_unused_2732_; 
v_unused_2728_ = lean_ctor_get(v_r_2243_, 4);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v_r_2243_, 3);
lean_dec(v_unused_2729_);
v_unused_2730_ = lean_ctor_get(v_r_2243_, 2);
lean_dec(v_unused_2730_);
v_unused_2731_ = lean_ctor_get(v_r_2243_, 1);
lean_dec(v_unused_2731_);
v_unused_2732_ = lean_ctor_get(v_r_2243_, 0);
lean_dec(v_unused_2732_);
v___x_2576_ = v_r_2243_;
v_isShared_2577_ = v_isSharedCheck_2727_;
goto v_resetjp_2575_;
}
else
{
lean_dec(v_r_2243_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2727_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v_tree_2579_; 
v___x_2578_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2428_, v_v_2429_, v_l_2430_, v_r_2431_);
v_tree_2579_ = lean_ctor_get(v___x_2578_, 2);
lean_inc(v_tree_2579_);
if (lean_obj_tag(v_tree_2579_) == 0)
{
lean_object* v_k_2580_; lean_object* v_v_2581_; lean_object* v_size_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; 
v_k_2580_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_k_2580_);
v_v_2581_ = lean_ctor_get(v___x_2578_, 1);
lean_inc(v_v_2581_);
lean_dec_ref(v___x_2578_);
v_size_2582_ = lean_ctor_get(v_tree_2579_, 0);
v___x_2583_ = lean_unsigned_to_nat(3u);
v___x_2584_ = lean_nat_mul(v___x_2583_, v_size_2582_);
v___x_2585_ = lean_nat_dec_lt(v___x_2584_, v_size_2422_);
lean_dec(v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_dec(v_r_2426_);
v___x_2586_ = lean_nat_add(v___x_2432_, v_size_2422_);
v___x_2587_ = lean_nat_add(v___x_2586_, v_size_2582_);
lean_dec(v___x_2586_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 4, v_tree_2579_);
lean_ctor_set(v___x_2576_, 3, v_l_2242_);
lean_ctor_set(v___x_2576_, 2, v_v_2581_);
lean_ctor_set(v___x_2576_, 1, v_k_2580_);
lean_ctor_set(v___x_2576_, 0, v___x_2587_);
v___x_2589_ = v___x_2576_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_k_2580_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_v_2581_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_l_2242_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_tree_2579_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
else
{
lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2656_; 
lean_inc(v_l_2425_);
lean_inc(v_v_2424_);
lean_inc(v_k_2423_);
lean_inc(v_size_2422_);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_l_2242_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; lean_object* v_unused_2658_; lean_object* v_unused_2659_; lean_object* v_unused_2660_; lean_object* v_unused_2661_; 
v_unused_2657_ = lean_ctor_get(v_l_2242_, 4);
lean_dec(v_unused_2657_);
v_unused_2658_ = lean_ctor_get(v_l_2242_, 3);
lean_dec(v_unused_2658_);
v_unused_2659_ = lean_ctor_get(v_l_2242_, 2);
lean_dec(v_unused_2659_);
v_unused_2660_ = lean_ctor_get(v_l_2242_, 1);
lean_dec(v_unused_2660_);
v_unused_2661_ = lean_ctor_get(v_l_2242_, 0);
lean_dec(v_unused_2661_);
v___x_2592_ = v_l_2242_;
v_isShared_2593_ = v_isSharedCheck_2656_;
goto v_resetjp_2591_;
}
else
{
lean_dec(v_l_2242_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2656_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v_size_2594_; lean_object* v_size_2595_; lean_object* v_k_2596_; lean_object* v_v_2597_; lean_object* v_l_2598_; lean_object* v_r_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v_size_2594_ = lean_ctor_get(v_l_2425_, 0);
v_size_2595_ = lean_ctor_get(v_r_2426_, 0);
v_k_2596_ = lean_ctor_get(v_r_2426_, 1);
v_v_2597_ = lean_ctor_get(v_r_2426_, 2);
v_l_2598_ = lean_ctor_get(v_r_2426_, 3);
v_r_2599_ = lean_ctor_get(v_r_2426_, 4);
v___x_2600_ = lean_unsigned_to_nat(2u);
v___x_2601_ = lean_nat_mul(v___x_2600_, v_size_2594_);
v___x_2602_ = lean_nat_dec_lt(v_size_2595_, v___x_2601_);
lean_dec(v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2640_; 
lean_inc(v_r_2599_);
lean_inc(v_l_2598_);
lean_inc(v_v_2597_);
lean_inc(v_k_2596_);
lean_del_object(v___x_2592_);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_r_2426_);
if (v_isSharedCheck_2640_ == 0)
{
lean_object* v_unused_2641_; lean_object* v_unused_2642_; lean_object* v_unused_2643_; lean_object* v_unused_2644_; lean_object* v_unused_2645_; 
v_unused_2641_ = lean_ctor_get(v_r_2426_, 4);
lean_dec(v_unused_2641_);
v_unused_2642_ = lean_ctor_get(v_r_2426_, 3);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v_r_2426_, 2);
lean_dec(v_unused_2643_);
v_unused_2644_ = lean_ctor_get(v_r_2426_, 1);
lean_dec(v_unused_2644_);
v_unused_2645_ = lean_ctor_get(v_r_2426_, 0);
lean_dec(v_unused_2645_);
v___x_2604_ = v_r_2426_;
v_isShared_2605_ = v_isSharedCheck_2640_;
goto v_resetjp_2603_;
}
else
{
lean_dec(v_r_2426_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2640_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___x_2628_; lean_object* v___y_2630_; 
v___x_2606_ = lean_nat_add(v___x_2432_, v_size_2422_);
lean_dec(v_size_2422_);
v___x_2607_ = lean_nat_add(v___x_2606_, v_size_2582_);
lean_dec(v___x_2606_);
v___x_2628_ = lean_nat_add(v___x_2432_, v_size_2594_);
if (lean_obj_tag(v_l_2598_) == 0)
{
lean_object* v_size_2638_; 
v_size_2638_ = lean_ctor_get(v_l_2598_, 0);
lean_inc(v_size_2638_);
v___y_2630_ = v_size_2638_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_unsigned_to_nat(0u);
v___y_2630_ = v___x_2639_;
goto v___jp_2629_;
}
v___jp_2608_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = lean_nat_add(v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec(v___y_2610_);
lean_inc_ref(v_tree_2579_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 4, v_tree_2579_);
lean_ctor_set(v___x_2604_, 3, v_r_2599_);
lean_ctor_set(v___x_2604_, 2, v_v_2581_);
lean_ctor_set(v___x_2604_, 1, v_k_2580_);
lean_ctor_set(v___x_2604_, 0, v___x_2612_);
v___x_2614_ = v___x_2604_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_k_2580_);
lean_ctor_set(v_reuseFailAlloc_2627_, 2, v_v_2581_);
lean_ctor_set(v_reuseFailAlloc_2627_, 3, v_r_2599_);
lean_ctor_set(v_reuseFailAlloc_2627_, 4, v_tree_2579_);
v___x_2614_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v_isSharedCheck_2621_ = !lean_is_exclusive(v_tree_2579_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; lean_object* v_unused_2623_; lean_object* v_unused_2624_; lean_object* v_unused_2625_; lean_object* v_unused_2626_; 
v_unused_2622_ = lean_ctor_get(v_tree_2579_, 4);
lean_dec(v_unused_2622_);
v_unused_2623_ = lean_ctor_get(v_tree_2579_, 3);
lean_dec(v_unused_2623_);
v_unused_2624_ = lean_ctor_get(v_tree_2579_, 2);
lean_dec(v_unused_2624_);
v_unused_2625_ = lean_ctor_get(v_tree_2579_, 1);
lean_dec(v_unused_2625_);
v_unused_2626_ = lean_ctor_get(v_tree_2579_, 0);
lean_dec(v_unused_2626_);
v___x_2616_ = v_tree_2579_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_dec(v_tree_2579_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 4, v___x_2614_);
lean_ctor_set(v___x_2616_, 3, v___y_2609_);
lean_ctor_set(v___x_2616_, 2, v_v_2597_);
lean_ctor_set(v___x_2616_, 1, v_k_2596_);
lean_ctor_set(v___x_2616_, 0, v___x_2607_);
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_k_2596_);
lean_ctor_set(v_reuseFailAlloc_2620_, 2, v_v_2597_);
lean_ctor_set(v_reuseFailAlloc_2620_, 3, v___y_2609_);
lean_ctor_set(v_reuseFailAlloc_2620_, 4, v___x_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
v___jp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2631_ = lean_nat_add(v___x_2628_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec(v___x_2628_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 4, v_l_2598_);
lean_ctor_set(v___x_2576_, 3, v_l_2425_);
lean_ctor_set(v___x_2576_, 2, v_v_2424_);
lean_ctor_set(v___x_2576_, 1, v_k_2423_);
lean_ctor_set(v___x_2576_, 0, v___x_2631_);
v___x_2633_ = v___x_2576_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_k_2423_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_v_2424_);
lean_ctor_set(v_reuseFailAlloc_2637_, 3, v_l_2425_);
lean_ctor_set(v_reuseFailAlloc_2637_, 4, v_l_2598_);
v___x_2633_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_nat_add(v___x_2432_, v_size_2582_);
if (lean_obj_tag(v_r_2599_) == 0)
{
lean_object* v_size_2635_; 
v_size_2635_ = lean_ctor_get(v_r_2599_, 0);
lean_inc(v_size_2635_);
v___y_2609_ = v___x_2633_;
v___y_2610_ = v___x_2634_;
v___y_2611_ = v_size_2635_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_unsigned_to_nat(0u);
v___y_2609_ = v___x_2633_;
v___y_2610_ = v___x_2634_;
v___y_2611_ = v___x_2636_;
goto v___jp_2608_;
}
}
}
}
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2646_ = lean_nat_add(v___x_2432_, v_size_2422_);
lean_dec(v_size_2422_);
v___x_2647_ = lean_nat_add(v___x_2646_, v_size_2582_);
lean_dec(v___x_2646_);
v___x_2648_ = lean_nat_add(v___x_2432_, v_size_2582_);
v___x_2649_ = lean_nat_add(v___x_2648_, v_size_2595_);
lean_dec(v___x_2648_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 4, v_tree_2579_);
lean_ctor_set(v___x_2576_, 3, v_r_2426_);
lean_ctor_set(v___x_2576_, 2, v_v_2581_);
lean_ctor_set(v___x_2576_, 1, v_k_2580_);
lean_ctor_set(v___x_2576_, 0, v___x_2649_);
v___x_2651_ = v___x_2576_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_k_2580_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_v_2581_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_r_2426_);
lean_ctor_set(v_reuseFailAlloc_2655_, 4, v_tree_2579_);
v___x_2651_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2653_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v___x_2651_);
lean_ctor_set(v___x_2592_, 0, v___x_2647_);
v___x_2653_ = v___x_2592_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_k_2423_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_v_2424_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v_l_2425_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2425_) == 0)
{
lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2685_; 
lean_inc_ref(v_l_2425_);
lean_inc(v_v_2424_);
lean_inc(v_k_2423_);
lean_inc(v_size_2422_);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_l_2242_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; lean_object* v_unused_2687_; lean_object* v_unused_2688_; lean_object* v_unused_2689_; lean_object* v_unused_2690_; 
v_unused_2686_ = lean_ctor_get(v_l_2242_, 4);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_l_2242_, 3);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_l_2242_, 2);
lean_dec(v_unused_2688_);
v_unused_2689_ = lean_ctor_get(v_l_2242_, 1);
lean_dec(v_unused_2689_);
v_unused_2690_ = lean_ctor_get(v_l_2242_, 0);
lean_dec(v_unused_2690_);
v___x_2663_ = v_l_2242_;
v_isShared_2664_ = v_isSharedCheck_2685_;
goto v_resetjp_2662_;
}
else
{
lean_dec(v_l_2242_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2685_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
if (lean_obj_tag(v_r_2426_) == 0)
{
lean_object* v_k_2665_; lean_object* v_v_2666_; lean_object* v_size_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
v_k_2665_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_k_2665_);
v_v_2666_ = lean_ctor_get(v___x_2578_, 1);
lean_inc(v_v_2666_);
lean_dec_ref(v___x_2578_);
v_size_2667_ = lean_ctor_get(v_r_2426_, 0);
v___x_2668_ = lean_nat_add(v___x_2432_, v_size_2422_);
lean_dec(v_size_2422_);
v___x_2669_ = lean_nat_add(v___x_2432_, v_size_2667_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 4, v_tree_2579_);
lean_ctor_set(v___x_2576_, 3, v_r_2426_);
lean_ctor_set(v___x_2576_, 2, v_v_2666_);
lean_ctor_set(v___x_2576_, 1, v_k_2665_);
lean_ctor_set(v___x_2576_, 0, v___x_2669_);
v___x_2671_ = v___x_2576_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_k_2665_);
lean_ctor_set(v_reuseFailAlloc_2675_, 2, v_v_2666_);
lean_ctor_set(v_reuseFailAlloc_2675_, 3, v_r_2426_);
lean_ctor_set(v_reuseFailAlloc_2675_, 4, v_tree_2579_);
v___x_2671_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2673_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 4, v___x_2671_);
lean_ctor_set(v___x_2663_, 0, v___x_2668_);
v___x_2673_ = v___x_2663_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_k_2423_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v_v_2424_);
lean_ctor_set(v_reuseFailAlloc_2674_, 3, v_l_2425_);
lean_ctor_set(v_reuseFailAlloc_2674_, 4, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
lean_object* v_k_2676_; lean_object* v_v_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
lean_dec(v_size_2422_);
v_k_2676_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_k_2676_);
v_v_2677_ = lean_ctor_get(v___x_2578_, 1);
lean_inc(v_v_2677_);
lean_dec_ref(v___x_2578_);
v___x_2678_ = lean_unsigned_to_nat(3u);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 4, v_r_2426_);
lean_ctor_set(v___x_2576_, 3, v_r_2426_);
lean_ctor_set(v___x_2576_, 2, v_v_2677_);
lean_ctor_set(v___x_2576_, 1, v_k_2676_);
lean_ctor_set(v___x_2576_, 0, v___x_2432_);
v___x_2680_ = v___x_2576_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_k_2676_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_v_2677_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_r_2426_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_r_2426_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 4, v___x_2680_);
lean_ctor_set(v___x_2663_, 0, v___x_2678_);
v___x_2682_ = v___x_2663_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_k_2423_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_v_2424_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_l_2425_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2426_) == 0)
{
lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2715_; 
lean_inc(v_l_2425_);
lean_inc(v_v_2424_);
lean_inc(v_k_2423_);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_l_2242_);
if (v_isSharedCheck_2715_ == 0)
{
lean_object* v_unused_2716_; lean_object* v_unused_2717_; lean_object* v_unused_2718_; lean_object* v_unused_2719_; lean_object* v_unused_2720_; 
v_unused_2716_ = lean_ctor_get(v_l_2242_, 4);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_l_2242_, 3);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_l_2242_, 2);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_l_2242_, 1);
lean_dec(v_unused_2719_);
v_unused_2720_ = lean_ctor_get(v_l_2242_, 0);
lean_dec(v_unused_2720_);
v___x_2692_ = v_l_2242_;
v_isShared_2693_ = v_isSharedCheck_2715_;
goto v_resetjp_2691_;
}
else
{
lean_dec(v_l_2242_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2715_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_k_2694_; lean_object* v_v_2695_; lean_object* v_k_2696_; lean_object* v_v_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2711_; 
v_k_2694_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_k_2694_);
v_v_2695_ = lean_ctor_get(v___x_2578_, 1);
lean_inc(v_v_2695_);
lean_dec_ref(v___x_2578_);
v_k_2696_ = lean_ctor_get(v_r_2426_, 1);
v_v_2697_ = lean_ctor_get(v_r_2426_, 2);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_r_2426_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; lean_object* v_unused_2713_; lean_object* v_unused_2714_; 
v_unused_2712_ = lean_ctor_get(v_r_2426_, 4);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_r_2426_, 3);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_r_2426_, 0);
lean_dec(v_unused_2714_);
v___x_2699_ = v_r_2426_;
v_isShared_2700_ = v_isSharedCheck_2711_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_v_2697_);
lean_inc(v_k_2696_);
lean_dec(v_r_2426_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2711_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2701_ = lean_unsigned_to_nat(3u);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 4, v_l_2425_);
lean_ctor_set(v___x_2699_, 3, v_l_2425_);
lean_ctor_set(v___x_2699_, 2, v_v_2424_);
lean_ctor_set(v___x_2699_, 1, v_k_2423_);
lean_ctor_set(v___x_2699_, 0, v___x_2432_);
v___x_2703_ = v___x_2699_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_k_2423_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_v_2424_);
lean_ctor_set(v_reuseFailAlloc_2710_, 3, v_l_2425_);
lean_ctor_set(v_reuseFailAlloc_2710_, 4, v_l_2425_);
v___x_2703_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2705_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 4, v_l_2425_);
lean_ctor_set(v___x_2576_, 3, v_l_2425_);
lean_ctor_set(v___x_2576_, 2, v_v_2695_);
lean_ctor_set(v___x_2576_, 1, v_k_2694_);
lean_ctor_set(v___x_2576_, 0, v___x_2432_);
v___x_2705_ = v___x_2576_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_k_2694_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_v_2695_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_l_2425_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v_l_2425_);
v___x_2705_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2707_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 4, v___x_2705_);
lean_ctor_set(v___x_2692_, 3, v___x_2703_);
lean_ctor_set(v___x_2692_, 2, v_v_2697_);
lean_ctor_set(v___x_2692_, 1, v_k_2696_);
lean_ctor_set(v___x_2692_, 0, v___x_2701_);
v___x_2707_ = v___x_2692_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_k_2696_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_v_2697_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2708_, 4, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
}
else
{
lean_object* v_k_2721_; lean_object* v_v_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v_k_2721_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_k_2721_);
v_v_2722_ = lean_ctor_get(v___x_2578_, 1);
lean_inc(v_v_2722_);
lean_dec_ref(v___x_2578_);
v___x_2723_ = lean_unsigned_to_nat(2u);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 4, v_r_2426_);
lean_ctor_set(v___x_2576_, 3, v_l_2242_);
lean_ctor_set(v___x_2576_, 2, v_v_2722_);
lean_ctor_set(v___x_2576_, 1, v_k_2721_);
lean_ctor_set(v___x_2576_, 0, v___x_2723_);
v___x_2725_ = v___x_2576_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_k_2721_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_v_2722_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_l_2242_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v_r_2426_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
}
}
else
{
return v_l_2242_;
}
}
else
{
return v_r_2243_;
}
}
default: 
{
lean_object* v_impl_2733_; lean_object* v___x_2734_; 
v_impl_2733_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2238_, v_r_2243_);
v___x_2734_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2733_) == 0)
{
if (lean_obj_tag(v_l_2242_) == 0)
{
lean_object* v_size_2735_; lean_object* v_size_2736_; lean_object* v_k_2737_; lean_object* v_v_2738_; lean_object* v_l_2739_; lean_object* v_r_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_size_2735_ = lean_ctor_get(v_impl_2733_, 0);
v_size_2736_ = lean_ctor_get(v_l_2242_, 0);
v_k_2737_ = lean_ctor_get(v_l_2242_, 1);
v_v_2738_ = lean_ctor_get(v_l_2242_, 2);
v_l_2739_ = lean_ctor_get(v_l_2242_, 3);
v_r_2740_ = lean_ctor_get(v_l_2242_, 4);
lean_inc(v_r_2740_);
v___x_2741_ = lean_unsigned_to_nat(3u);
v___x_2742_ = lean_nat_mul(v___x_2741_, v_size_2735_);
v___x_2743_ = lean_nat_dec_lt(v___x_2742_, v_size_2736_);
lean_dec(v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
lean_dec(v_r_2740_);
v___x_2744_ = lean_nat_add(v___x_2734_, v_size_2736_);
v___x_2745_ = lean_nat_add(v___x_2744_, v_size_2735_);
lean_dec(v___x_2744_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v_impl_2733_);
lean_ctor_set(v___x_2245_, 0, v___x_2745_);
v___x_2747_ = v___x_2245_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_l_2242_);
lean_ctor_set(v_reuseFailAlloc_2748_, 4, v_impl_2733_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
else
{
lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2814_; 
lean_inc(v_l_2739_);
lean_inc(v_v_2738_);
lean_inc(v_k_2737_);
lean_inc(v_size_2736_);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_l_2242_);
if (v_isSharedCheck_2814_ == 0)
{
lean_object* v_unused_2815_; lean_object* v_unused_2816_; lean_object* v_unused_2817_; lean_object* v_unused_2818_; lean_object* v_unused_2819_; 
v_unused_2815_ = lean_ctor_get(v_l_2242_, 4);
lean_dec(v_unused_2815_);
v_unused_2816_ = lean_ctor_get(v_l_2242_, 3);
lean_dec(v_unused_2816_);
v_unused_2817_ = lean_ctor_get(v_l_2242_, 2);
lean_dec(v_unused_2817_);
v_unused_2818_ = lean_ctor_get(v_l_2242_, 1);
lean_dec(v_unused_2818_);
v_unused_2819_ = lean_ctor_get(v_l_2242_, 0);
lean_dec(v_unused_2819_);
v___x_2750_ = v_l_2242_;
v_isShared_2751_ = v_isSharedCheck_2814_;
goto v_resetjp_2749_;
}
else
{
lean_dec(v_l_2242_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2814_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_size_2752_; lean_object* v_size_2753_; lean_object* v_k_2754_; lean_object* v_v_2755_; lean_object* v_l_2756_; lean_object* v_r_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v_size_2752_ = lean_ctor_get(v_l_2739_, 0);
v_size_2753_ = lean_ctor_get(v_r_2740_, 0);
v_k_2754_ = lean_ctor_get(v_r_2740_, 1);
v_v_2755_ = lean_ctor_get(v_r_2740_, 2);
v_l_2756_ = lean_ctor_get(v_r_2740_, 3);
v_r_2757_ = lean_ctor_get(v_r_2740_, 4);
v___x_2758_ = lean_unsigned_to_nat(2u);
v___x_2759_ = lean_nat_mul(v___x_2758_, v_size_2752_);
v___x_2760_ = lean_nat_dec_lt(v_size_2753_, v___x_2759_);
lean_dec(v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2789_; 
lean_inc(v_r_2757_);
lean_inc(v_l_2756_);
lean_inc(v_v_2755_);
lean_inc(v_k_2754_);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_r_2740_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; lean_object* v_unused_2791_; lean_object* v_unused_2792_; lean_object* v_unused_2793_; lean_object* v_unused_2794_; 
v_unused_2790_ = lean_ctor_get(v_r_2740_, 4);
lean_dec(v_unused_2790_);
v_unused_2791_ = lean_ctor_get(v_r_2740_, 3);
lean_dec(v_unused_2791_);
v_unused_2792_ = lean_ctor_get(v_r_2740_, 2);
lean_dec(v_unused_2792_);
v_unused_2793_ = lean_ctor_get(v_r_2740_, 1);
lean_dec(v_unused_2793_);
v_unused_2794_ = lean_ctor_get(v_r_2740_, 0);
lean_dec(v_unused_2794_);
v___x_2762_ = v_r_2740_;
v_isShared_2763_ = v_isSharedCheck_2789_;
goto v_resetjp_2761_;
}
else
{
lean_dec(v_r_2740_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2789_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___x_2777_; lean_object* v___y_2779_; 
v___x_2764_ = lean_nat_add(v___x_2734_, v_size_2736_);
lean_dec(v_size_2736_);
v___x_2765_ = lean_nat_add(v___x_2764_, v_size_2735_);
lean_dec(v___x_2764_);
v___x_2777_ = lean_nat_add(v___x_2734_, v_size_2752_);
if (lean_obj_tag(v_l_2756_) == 0)
{
lean_object* v_size_2787_; 
v_size_2787_ = lean_ctor_get(v_l_2756_, 0);
lean_inc(v_size_2787_);
v___y_2779_ = v_size_2787_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_unsigned_to_nat(0u);
v___y_2779_ = v___x_2788_;
goto v___jp_2778_;
}
v___jp_2766_:
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2770_ = lean_nat_add(v___y_2767_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec(v___y_2767_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 4, v_impl_2733_);
lean_ctor_set(v___x_2762_, 3, v_r_2757_);
lean_ctor_set(v___x_2762_, 2, v_v_2241_);
lean_ctor_set(v___x_2762_, 1, v_k_2240_);
lean_ctor_set(v___x_2762_, 0, v___x_2770_);
v___x_2772_ = v___x_2762_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2776_, 3, v_r_2757_);
lean_ctor_set(v_reuseFailAlloc_2776_, 4, v_impl_2733_);
v___x_2772_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2774_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 4, v___x_2772_);
lean_ctor_set(v___x_2750_, 3, v___y_2768_);
lean_ctor_set(v___x_2750_, 2, v_v_2755_);
lean_ctor_set(v___x_2750_, 1, v_k_2754_);
lean_ctor_set(v___x_2750_, 0, v___x_2765_);
v___x_2774_ = v___x_2750_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_k_2754_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_v_2755_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v___y_2768_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
v___jp_2778_:
{
lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2780_ = lean_nat_add(v___x_2777_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec(v___x_2777_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v_l_2756_);
lean_ctor_set(v___x_2245_, 3, v_l_2739_);
lean_ctor_set(v___x_2245_, 2, v_v_2738_);
lean_ctor_set(v___x_2245_, 1, v_k_2737_);
lean_ctor_set(v___x_2245_, 0, v___x_2780_);
v___x_2782_ = v___x_2245_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_k_2737_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_v_2738_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v_l_2739_);
lean_ctor_set(v_reuseFailAlloc_2786_, 4, v_l_2756_);
v___x_2782_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_nat_add(v___x_2734_, v_size_2735_);
if (lean_obj_tag(v_r_2757_) == 0)
{
lean_object* v_size_2784_; 
v_size_2784_ = lean_ctor_get(v_r_2757_, 0);
lean_inc(v_size_2784_);
v___y_2767_ = v___x_2783_;
v___y_2768_ = v___x_2782_;
v___y_2769_ = v_size_2784_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_unsigned_to_nat(0u);
v___y_2767_ = v___x_2783_;
v___y_2768_ = v___x_2782_;
v___y_2769_ = v___x_2785_;
goto v___jp_2766_;
}
}
}
}
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
lean_del_object(v___x_2245_);
v___x_2795_ = lean_nat_add(v___x_2734_, v_size_2736_);
lean_dec(v_size_2736_);
v___x_2796_ = lean_nat_add(v___x_2795_, v_size_2735_);
lean_dec(v___x_2795_);
v___x_2797_ = lean_nat_add(v___x_2734_, v_size_2735_);
v___x_2798_ = lean_nat_add(v___x_2797_, v_size_2753_);
lean_dec(v___x_2797_);
lean_inc_ref(v_impl_2733_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 4, v_impl_2733_);
lean_ctor_set(v___x_2750_, 3, v_r_2740_);
lean_ctor_set(v___x_2750_, 2, v_v_2241_);
lean_ctor_set(v___x_2750_, 1, v_k_2240_);
lean_ctor_set(v___x_2750_, 0, v___x_2798_);
v___x_2800_ = v___x_2750_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_r_2740_);
lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_impl_2733_);
v___x_2800_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_isSharedCheck_2807_ = !lean_is_exclusive(v_impl_2733_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; lean_object* v_unused_2809_; lean_object* v_unused_2810_; lean_object* v_unused_2811_; lean_object* v_unused_2812_; 
v_unused_2808_ = lean_ctor_get(v_impl_2733_, 4);
lean_dec(v_unused_2808_);
v_unused_2809_ = lean_ctor_get(v_impl_2733_, 3);
lean_dec(v_unused_2809_);
v_unused_2810_ = lean_ctor_get(v_impl_2733_, 2);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_impl_2733_, 1);
lean_dec(v_unused_2811_);
v_unused_2812_ = lean_ctor_get(v_impl_2733_, 0);
lean_dec(v_unused_2812_);
v___x_2802_ = v_impl_2733_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_dec(v_impl_2733_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 4, v___x_2800_);
lean_ctor_set(v___x_2802_, 3, v_l_2739_);
lean_ctor_set(v___x_2802_, 2, v_v_2738_);
lean_ctor_set(v___x_2802_, 1, v_k_2737_);
lean_ctor_set(v___x_2802_, 0, v___x_2796_);
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_k_2737_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_v_2738_);
lean_ctor_set(v_reuseFailAlloc_2806_, 3, v_l_2739_);
lean_ctor_set(v_reuseFailAlloc_2806_, 4, v___x_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v_size_2820_ = lean_ctor_get(v_impl_2733_, 0);
v___x_2821_ = lean_nat_add(v___x_2734_, v_size_2820_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v_impl_2733_);
lean_ctor_set(v___x_2245_, 0, v___x_2821_);
v___x_2823_ = v___x_2245_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2824_, 3, v_l_2242_);
lean_ctor_set(v_reuseFailAlloc_2824_, 4, v_impl_2733_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
else
{
if (lean_obj_tag(v_l_2242_) == 0)
{
lean_object* v_l_2825_; 
v_l_2825_ = lean_ctor_get(v_l_2242_, 3);
if (lean_obj_tag(v_l_2825_) == 0)
{
lean_object* v_r_2826_; 
lean_inc_ref(v_l_2825_);
v_r_2826_ = lean_ctor_get(v_l_2242_, 4);
lean_inc(v_r_2826_);
if (lean_obj_tag(v_r_2826_) == 0)
{
lean_object* v_size_2827_; lean_object* v_k_2828_; lean_object* v_v_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2842_; 
v_size_2827_ = lean_ctor_get(v_l_2242_, 0);
v_k_2828_ = lean_ctor_get(v_l_2242_, 1);
v_v_2829_ = lean_ctor_get(v_l_2242_, 2);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_l_2242_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; lean_object* v_unused_2844_; 
v_unused_2843_ = lean_ctor_get(v_l_2242_, 4);
lean_dec(v_unused_2843_);
v_unused_2844_ = lean_ctor_get(v_l_2242_, 3);
lean_dec(v_unused_2844_);
v___x_2831_ = v_l_2242_;
v_isShared_2832_ = v_isSharedCheck_2842_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_v_2829_);
lean_inc(v_k_2828_);
lean_inc(v_size_2827_);
lean_dec(v_l_2242_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2842_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v_size_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v_size_2833_ = lean_ctor_get(v_r_2826_, 0);
v___x_2834_ = lean_nat_add(v___x_2734_, v_size_2827_);
lean_dec(v_size_2827_);
v___x_2835_ = lean_nat_add(v___x_2734_, v_size_2833_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 4, v_impl_2733_);
lean_ctor_set(v___x_2831_, 3, v_r_2826_);
lean_ctor_set(v___x_2831_, 2, v_v_2241_);
lean_ctor_set(v___x_2831_, 1, v_k_2240_);
lean_ctor_set(v___x_2831_, 0, v___x_2835_);
v___x_2837_ = v___x_2831_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2841_, 3, v_r_2826_);
lean_ctor_set(v_reuseFailAlloc_2841_, 4, v_impl_2733_);
v___x_2837_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2839_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v___x_2837_);
lean_ctor_set(v___x_2245_, 3, v_l_2825_);
lean_ctor_set(v___x_2245_, 2, v_v_2829_);
lean_ctor_set(v___x_2245_, 1, v_k_2828_);
lean_ctor_set(v___x_2245_, 0, v___x_2834_);
v___x_2839_ = v___x_2245_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_k_2828_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_v_2829_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_l_2825_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v_k_2845_; lean_object* v_v_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2857_; 
v_k_2845_ = lean_ctor_get(v_l_2242_, 1);
v_v_2846_ = lean_ctor_get(v_l_2242_, 2);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_l_2242_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; lean_object* v_unused_2859_; lean_object* v_unused_2860_; 
v_unused_2858_ = lean_ctor_get(v_l_2242_, 4);
lean_dec(v_unused_2858_);
v_unused_2859_ = lean_ctor_get(v_l_2242_, 3);
lean_dec(v_unused_2859_);
v_unused_2860_ = lean_ctor_get(v_l_2242_, 0);
lean_dec(v_unused_2860_);
v___x_2848_ = v_l_2242_;
v_isShared_2849_ = v_isSharedCheck_2857_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_v_2846_);
lean_inc(v_k_2845_);
lean_dec(v_l_2242_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2857_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2850_ = lean_unsigned_to_nat(3u);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 3, v_r_2826_);
lean_ctor_set(v___x_2848_, 2, v_v_2241_);
lean_ctor_set(v___x_2848_, 1, v_k_2240_);
lean_ctor_set(v___x_2848_, 0, v___x_2734_);
v___x_2852_ = v___x_2848_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_r_2826_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v_r_2826_);
v___x_2852_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2854_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v___x_2852_);
lean_ctor_set(v___x_2245_, 3, v_l_2825_);
lean_ctor_set(v___x_2245_, 2, v_v_2846_);
lean_ctor_set(v___x_2245_, 1, v_k_2845_);
lean_ctor_set(v___x_2245_, 0, v___x_2850_);
v___x_2854_ = v___x_2245_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_k_2845_);
lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_v_2846_);
lean_ctor_set(v_reuseFailAlloc_2855_, 3, v_l_2825_);
lean_ctor_set(v_reuseFailAlloc_2855_, 4, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
}
else
{
lean_object* v_r_2861_; 
v_r_2861_ = lean_ctor_get(v_l_2242_, 4);
lean_inc(v_r_2861_);
if (lean_obj_tag(v_r_2861_) == 0)
{
lean_object* v_k_2862_; lean_object* v_v_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2886_; 
lean_inc(v_l_2825_);
v_k_2862_ = lean_ctor_get(v_l_2242_, 1);
v_v_2863_ = lean_ctor_get(v_l_2242_, 2);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_l_2242_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; lean_object* v_unused_2888_; lean_object* v_unused_2889_; 
v_unused_2887_ = lean_ctor_get(v_l_2242_, 4);
lean_dec(v_unused_2887_);
v_unused_2888_ = lean_ctor_get(v_l_2242_, 3);
lean_dec(v_unused_2888_);
v_unused_2889_ = lean_ctor_get(v_l_2242_, 0);
lean_dec(v_unused_2889_);
v___x_2865_ = v_l_2242_;
v_isShared_2866_ = v_isSharedCheck_2886_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_v_2863_);
lean_inc(v_k_2862_);
lean_dec(v_l_2242_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2886_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v_k_2867_; lean_object* v_v_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2882_; 
v_k_2867_ = lean_ctor_get(v_r_2861_, 1);
v_v_2868_ = lean_ctor_get(v_r_2861_, 2);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_r_2861_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; lean_object* v_unused_2884_; lean_object* v_unused_2885_; 
v_unused_2883_ = lean_ctor_get(v_r_2861_, 4);
lean_dec(v_unused_2883_);
v_unused_2884_ = lean_ctor_get(v_r_2861_, 3);
lean_dec(v_unused_2884_);
v_unused_2885_ = lean_ctor_get(v_r_2861_, 0);
lean_dec(v_unused_2885_);
v___x_2870_ = v_r_2861_;
v_isShared_2871_ = v_isSharedCheck_2882_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_v_2868_);
lean_inc(v_k_2867_);
lean_dec(v_r_2861_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2882_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2872_ = lean_unsigned_to_nat(3u);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 4, v_l_2825_);
lean_ctor_set(v___x_2870_, 3, v_l_2825_);
lean_ctor_set(v___x_2870_, 2, v_v_2863_);
lean_ctor_set(v___x_2870_, 1, v_k_2862_);
lean_ctor_set(v___x_2870_, 0, v___x_2734_);
v___x_2874_ = v___x_2870_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_k_2862_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_v_2863_);
lean_ctor_set(v_reuseFailAlloc_2881_, 3, v_l_2825_);
lean_ctor_set(v_reuseFailAlloc_2881_, 4, v_l_2825_);
v___x_2874_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 4, v_l_2825_);
lean_ctor_set(v___x_2865_, 2, v_v_2241_);
lean_ctor_set(v___x_2865_, 1, v_k_2240_);
lean_ctor_set(v___x_2865_, 0, v___x_2734_);
v___x_2876_ = v___x_2865_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2880_, 3, v_l_2825_);
lean_ctor_set(v_reuseFailAlloc_2880_, 4, v_l_2825_);
v___x_2876_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2878_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v___x_2876_);
lean_ctor_set(v___x_2245_, 3, v___x_2874_);
lean_ctor_set(v___x_2245_, 2, v_v_2868_);
lean_ctor_set(v___x_2245_, 1, v_k_2867_);
lean_ctor_set(v___x_2245_, 0, v___x_2872_);
v___x_2878_ = v___x_2245_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_k_2867_);
lean_ctor_set(v_reuseFailAlloc_2879_, 2, v_v_2868_);
lean_ctor_set(v_reuseFailAlloc_2879_, 3, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2879_, 4, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2890_ = lean_unsigned_to_nat(2u);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v_r_2861_);
lean_ctor_set(v___x_2245_, 0, v___x_2890_);
v___x_2892_ = v___x_2245_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2893_, 3, v_l_2242_);
lean_ctor_set(v_reuseFailAlloc_2893_, 4, v_r_2861_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v___x_2895_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v_l_2242_);
lean_ctor_set(v___x_2245_, 0, v___x_2734_);
v___x_2895_ = v___x_2245_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v_l_2242_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v_l_2242_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
}
}
else
{
return v_t_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_2899_, lean_object* v_t_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2899_, v_t_2900_);
lean_dec(v_k_2899_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_2902_, lean_object* v_declName_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v_ext_2909_; lean_object* v_toEnvExtension_2910_; lean_object* v_env_2911_; lean_object* v_asyncMode_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; lean_object* v_funCC_2915_; lean_object* v___y_2917_; uint8_t v___x_2943_; 
v___x_2907_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2908_ = lean_st_ref_get(v_a_2905_);
v_ext_2909_ = lean_ctor_get(v_ext_2902_, 1);
v_toEnvExtension_2910_ = lean_ctor_get(v_ext_2909_, 0);
v_env_2911_ = lean_ctor_get(v___x_2908_, 0);
lean_inc_ref(v_env_2911_);
lean_dec(v___x_2908_);
v_asyncMode_2912_ = lean_ctor_get(v_toEnvExtension_2910_, 2);
v___x_2913_ = 0;
v___x_2914_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2907_, v_ext_2902_, v_env_2911_, v_asyncMode_2912_, v___x_2913_);
v_funCC_2915_ = lean_ctor_get(v___x_2914_, 2);
lean_inc(v_funCC_2915_);
lean_dec(v___x_2914_);
v___x_2943_ = l_Lean_NameSet_contains(v_funCC_2915_, v_declName_2903_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; 
lean_inc(v_declName_2903_);
v___x_2944_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_dec_ref_known(v___x_2944_, 1);
v___y_2917_ = v_a_2905_;
goto v___jp_2916_;
}
else
{
lean_dec(v_funCC_2915_);
lean_dec(v_declName_2903_);
lean_dec_ref(v_ext_2902_);
return v___x_2944_;
}
}
else
{
v___y_2917_ = v_a_2905_;
goto v___jp_2916_;
}
v___jp_2916_:
{
lean_object* v___x_2918_; lean_object* v___f_2919_; lean_object* v___x_2920_; lean_object* v_env_2921_; lean_object* v_nextMacroScope_2922_; lean_object* v_ngen_2923_; lean_object* v_auxDeclNGen_2924_; lean_object* v_traceState_2925_; lean_object* v_recordedDeps_2926_; lean_object* v_messages_2927_; lean_object* v_infoState_2928_; lean_object* v_snapshotTasks_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2941_; 
v___x_2918_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_2903_, v_funCC_2915_);
lean_dec(v_declName_2903_);
v___f_2919_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_2919_, 0, v___x_2918_);
v___x_2920_ = lean_st_ref_take(v___y_2917_);
v_env_2921_ = lean_ctor_get(v___x_2920_, 0);
v_nextMacroScope_2922_ = lean_ctor_get(v___x_2920_, 1);
v_ngen_2923_ = lean_ctor_get(v___x_2920_, 2);
v_auxDeclNGen_2924_ = lean_ctor_get(v___x_2920_, 3);
v_traceState_2925_ = lean_ctor_get(v___x_2920_, 4);
v_recordedDeps_2926_ = lean_ctor_get(v___x_2920_, 6);
v_messages_2927_ = lean_ctor_get(v___x_2920_, 7);
v_infoState_2928_ = lean_ctor_get(v___x_2920_, 8);
v_snapshotTasks_2929_ = lean_ctor_get(v___x_2920_, 9);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; 
v_unused_2942_ = lean_ctor_get(v___x_2920_, 5);
lean_dec(v_unused_2942_);
v___x_2931_ = v___x_2920_;
v_isShared_2932_ = v_isSharedCheck_2941_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_snapshotTasks_2929_);
lean_inc(v_infoState_2928_);
lean_inc(v_messages_2927_);
lean_inc(v_recordedDeps_2926_);
lean_inc(v_traceState_2925_);
lean_inc(v_auxDeclNGen_2924_);
lean_inc(v_ngen_2923_);
lean_inc(v_nextMacroScope_2922_);
lean_inc(v_env_2921_);
lean_dec(v___x_2920_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2941_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2933_ = lean_box(0);
v___x_2934_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2902_, v_env_2921_, v___f_2919_);
v___x_2935_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 5, v___x_2935_);
lean_ctor_set(v___x_2931_, 0, v___x_2934_);
v___x_2937_ = v___x_2931_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_nextMacroScope_2922_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_ngen_2923_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_auxDeclNGen_2924_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v_traceState_2925_);
lean_ctor_set(v_reuseFailAlloc_2940_, 5, v___x_2935_);
lean_ctor_set(v_reuseFailAlloc_2940_, 6, v_recordedDeps_2926_);
lean_ctor_set(v_reuseFailAlloc_2940_, 7, v_messages_2927_);
lean_ctor_set(v_reuseFailAlloc_2940_, 8, v_infoState_2928_);
lean_ctor_set(v_reuseFailAlloc_2940_, 9, v_snapshotTasks_2929_);
v___x_2937_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_st_ref_put(v___y_2917_, v___x_2937_);
v___x_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2933_);
return v___x_2939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_2945_, lean_object* v_declName_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2945_, v_declName_2946_, v_a_2947_, v_a_2948_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_2951_, lean_object* v_k_2952_, lean_object* v_t_2953_, lean_object* v_h_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2952_, v_t_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_2956_, lean_object* v_k_2957_, lean_object* v_t_2958_, lean_object* v_h_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_2956_, v_k_2957_, v_t_2958_, v_h_2959_);
lean_dec(v_k_2957_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_2961_, lean_object* v_s_2962_){
_start:
{
lean_object* v_casesTypes_2963_; lean_object* v_extThms_2964_; lean_object* v_funCC_2965_; lean_object* v_inj_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
v_casesTypes_2963_ = lean_ctor_get(v_s_2962_, 0);
v_extThms_2964_ = lean_ctor_get(v_s_2962_, 1);
v_funCC_2965_ = lean_ctor_get(v_s_2962_, 2);
v_inj_2966_ = lean_ctor_get(v_s_2962_, 4);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_s_2962_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; 
v_unused_2974_ = lean_ctor_get(v_s_2962_, 3);
lean_dec(v_unused_2974_);
v___x_2968_ = v_s_2962_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_inj_2966_);
lean_inc(v_funCC_2965_);
lean_inc(v_extThms_2964_);
lean_inc(v_casesTypes_2963_);
lean_dec(v_s_2962_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 3, v_a_2961_);
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_casesTypes_2963_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_extThms_2964_);
lean_ctor_set(v_reuseFailAlloc_2972_, 2, v_funCC_2965_);
lean_ctor_set(v_reuseFailAlloc_2972_, 3, v_a_2961_);
lean_ctor_set(v_reuseFailAlloc_2972_, 4, v_inj_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_2975_, lean_object* v_declName_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v_ext_2984_; lean_object* v_toEnvExtension_2985_; lean_object* v_env_2986_; lean_object* v_asyncMode_2987_; uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v_ematch_2990_; lean_object* v___x_2991_; 
v___x_2982_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2983_ = lean_st_ref_get(v_a_2980_);
v_ext_2984_ = lean_ctor_get(v_ext_2975_, 1);
v_toEnvExtension_2985_ = lean_ctor_get(v_ext_2984_, 0);
v_env_2986_ = lean_ctor_get(v___x_2983_, 0);
lean_inc_ref(v_env_2986_);
lean_dec(v___x_2983_);
v_asyncMode_2987_ = lean_ctor_get(v_toEnvExtension_2985_, 2);
v___x_2988_ = 0;
v___x_2989_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2982_, v_ext_2975_, v_env_2986_, v_asyncMode_2987_, v___x_2988_);
v_ematch_2990_ = lean_ctor_get(v___x_2989_, 3);
lean_inc_ref(v_ematch_2990_);
lean_dec(v___x_2989_);
v___x_2991_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_2990_, v_declName_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3037_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_2994_ = v___x_2991_;
v_isShared_2995_ = v_isSharedCheck_3037_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3037_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___f_2996_; lean_object* v___x_2997_; lean_object* v_env_2998_; lean_object* v_nextMacroScope_2999_; lean_object* v_ngen_3000_; lean_object* v_auxDeclNGen_3001_; lean_object* v_traceState_3002_; lean_object* v_recordedDeps_3003_; lean_object* v_messages_3004_; lean_object* v_infoState_3005_; lean_object* v_snapshotTasks_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3035_; 
v___f_2996_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_2996_, 0, v_a_2992_);
v___x_2997_ = lean_st_ref_take(v_a_2980_);
v_env_2998_ = lean_ctor_get(v___x_2997_, 0);
v_nextMacroScope_2999_ = lean_ctor_get(v___x_2997_, 1);
v_ngen_3000_ = lean_ctor_get(v___x_2997_, 2);
v_auxDeclNGen_3001_ = lean_ctor_get(v___x_2997_, 3);
v_traceState_3002_ = lean_ctor_get(v___x_2997_, 4);
v_recordedDeps_3003_ = lean_ctor_get(v___x_2997_, 6);
v_messages_3004_ = lean_ctor_get(v___x_2997_, 7);
v_infoState_3005_ = lean_ctor_get(v___x_2997_, 8);
v_snapshotTasks_3006_ = lean_ctor_get(v___x_2997_, 9);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3035_ == 0)
{
lean_object* v_unused_3036_; 
v_unused_3036_ = lean_ctor_get(v___x_2997_, 5);
lean_dec(v_unused_3036_);
v___x_3008_ = v___x_2997_;
v_isShared_3009_ = v_isSharedCheck_3035_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_snapshotTasks_3006_);
lean_inc(v_infoState_3005_);
lean_inc(v_messages_3004_);
lean_inc(v_recordedDeps_3003_);
lean_inc(v_traceState_3002_);
lean_inc(v_auxDeclNGen_3001_);
lean_inc(v_ngen_3000_);
lean_inc(v_nextMacroScope_2999_);
lean_inc(v_env_2998_);
lean_dec(v___x_2997_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3035_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3010_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2975_, v_env_2998_, v___f_2996_);
v___x_3011_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 5, v___x_3011_);
lean_ctor_set(v___x_3008_, 0, v___x_3010_);
v___x_3013_ = v___x_3008_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3010_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_nextMacroScope_2999_);
lean_ctor_set(v_reuseFailAlloc_3034_, 2, v_ngen_3000_);
lean_ctor_set(v_reuseFailAlloc_3034_, 3, v_auxDeclNGen_3001_);
lean_ctor_set(v_reuseFailAlloc_3034_, 4, v_traceState_3002_);
lean_ctor_set(v_reuseFailAlloc_3034_, 5, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3034_, 6, v_recordedDeps_3003_);
lean_ctor_set(v_reuseFailAlloc_3034_, 7, v_messages_3004_);
lean_ctor_set(v_reuseFailAlloc_3034_, 8, v_infoState_3005_);
lean_ctor_set(v_reuseFailAlloc_3034_, 9, v_snapshotTasks_3006_);
v___x_3013_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v_mctx_3016_; lean_object* v_zetaDeltaFVarIds_3017_; lean_object* v_postponed_3018_; lean_object* v_diag_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3032_; 
v___x_3014_ = lean_st_ref_put(v_a_2980_, v___x_3013_);
v___x_3015_ = lean_st_ref_take(v_a_2978_);
v_mctx_3016_ = lean_ctor_get(v___x_3015_, 0);
v_zetaDeltaFVarIds_3017_ = lean_ctor_get(v___x_3015_, 2);
v_postponed_3018_ = lean_ctor_get(v___x_3015_, 3);
v_diag_3019_ = lean_ctor_get(v___x_3015_, 4);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3032_ == 0)
{
lean_object* v_unused_3033_; 
v_unused_3033_ = lean_ctor_get(v___x_3015_, 1);
lean_dec(v_unused_3033_);
v___x_3021_ = v___x_3015_;
v_isShared_3022_ = v_isSharedCheck_3032_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_diag_3019_);
lean_inc(v_postponed_3018_);
lean_inc(v_zetaDeltaFVarIds_3017_);
lean_inc(v_mctx_3016_);
lean_dec(v___x_3015_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3032_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3023_ = lean_box(0);
v___x_3024_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v___x_3024_);
v___x_3026_ = v___x_3021_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_mctx_3016_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_zetaDeltaFVarIds_3017_);
lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_postponed_3018_);
lean_ctor_set(v_reuseFailAlloc_3031_, 4, v_diag_3019_);
v___x_3026_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___x_3027_ = lean_st_ref_put(v_a_2978_, v___x_3026_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_3023_);
v___x_3029_ = v___x_2994_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3023_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v_ext_2975_);
v_a_3038_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_2991_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_2991_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_3046_, lean_object* v_declName_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_3046_, v_declName_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_3054_, lean_object* v_s_3055_){
_start:
{
lean_object* v_casesTypes_3056_; lean_object* v_extThms_3057_; lean_object* v_funCC_3058_; lean_object* v_ematch_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
v_casesTypes_3056_ = lean_ctor_get(v_s_3055_, 0);
v_extThms_3057_ = lean_ctor_get(v_s_3055_, 1);
v_funCC_3058_ = lean_ctor_get(v_s_3055_, 2);
v_ematch_3059_ = lean_ctor_get(v_s_3055_, 3);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_s_3055_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; 
v_unused_3067_ = lean_ctor_get(v_s_3055_, 4);
lean_dec(v_unused_3067_);
v___x_3061_ = v_s_3055_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_ematch_3059_);
lean_inc(v_funCC_3058_);
lean_inc(v_extThms_3057_);
lean_inc(v_casesTypes_3056_);
lean_dec(v_s_3055_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 4, v_a_3054_);
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_casesTypes_3056_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_extThms_3057_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_funCC_3058_);
lean_ctor_set(v_reuseFailAlloc_3065_, 3, v_ematch_3059_);
lean_ctor_set(v_reuseFailAlloc_3065_, 4, v_a_3054_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_3068_, lean_object* v_declName_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v_ext_3077_; lean_object* v_toEnvExtension_3078_; lean_object* v_env_3079_; lean_object* v_asyncMode_3080_; uint8_t v___x_3081_; lean_object* v___x_3082_; lean_object* v_inj_3083_; lean_object* v___x_3084_; 
v___x_3075_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3076_ = lean_st_ref_get(v_a_3073_);
v_ext_3077_ = lean_ctor_get(v_ext_3068_, 1);
v_toEnvExtension_3078_ = lean_ctor_get(v_ext_3077_, 0);
v_env_3079_ = lean_ctor_get(v___x_3076_, 0);
lean_inc_ref(v_env_3079_);
lean_dec(v___x_3076_);
v_asyncMode_3080_ = lean_ctor_get(v_toEnvExtension_3078_, 2);
v___x_3081_ = 0;
v___x_3082_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3075_, v_ext_3068_, v_env_3079_, v_asyncMode_3080_, v___x_3081_);
v_inj_3083_ = lean_ctor_get(v___x_3082_, 4);
lean_inc_ref(v_inj_3083_);
lean_dec(v___x_3082_);
v___x_3084_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_3083_, v_declName_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3130_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3130_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3130_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___f_3089_; lean_object* v___x_3090_; lean_object* v_env_3091_; lean_object* v_nextMacroScope_3092_; lean_object* v_ngen_3093_; lean_object* v_auxDeclNGen_3094_; lean_object* v_traceState_3095_; lean_object* v_recordedDeps_3096_; lean_object* v_messages_3097_; lean_object* v_infoState_3098_; lean_object* v_snapshotTasks_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3128_; 
v___f_3089_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_3089_, 0, v_a_3085_);
v___x_3090_ = lean_st_ref_take(v_a_3073_);
v_env_3091_ = lean_ctor_get(v___x_3090_, 0);
v_nextMacroScope_3092_ = lean_ctor_get(v___x_3090_, 1);
v_ngen_3093_ = lean_ctor_get(v___x_3090_, 2);
v_auxDeclNGen_3094_ = lean_ctor_get(v___x_3090_, 3);
v_traceState_3095_ = lean_ctor_get(v___x_3090_, 4);
v_recordedDeps_3096_ = lean_ctor_get(v___x_3090_, 6);
v_messages_3097_ = lean_ctor_get(v___x_3090_, 7);
v_infoState_3098_ = lean_ctor_get(v___x_3090_, 8);
v_snapshotTasks_3099_ = lean_ctor_get(v___x_3090_, 9);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3128_ == 0)
{
lean_object* v_unused_3129_; 
v_unused_3129_ = lean_ctor_get(v___x_3090_, 5);
lean_dec(v_unused_3129_);
v___x_3101_ = v___x_3090_;
v_isShared_3102_ = v_isSharedCheck_3128_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_snapshotTasks_3099_);
lean_inc(v_infoState_3098_);
lean_inc(v_messages_3097_);
lean_inc(v_recordedDeps_3096_);
lean_inc(v_traceState_3095_);
lean_inc(v_auxDeclNGen_3094_);
lean_inc(v_ngen_3093_);
lean_inc(v_nextMacroScope_3092_);
lean_inc(v_env_3091_);
lean_dec(v___x_3090_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3128_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3103_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_3068_, v_env_3091_, v___f_3089_);
v___x_3104_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 5, v___x_3104_);
lean_ctor_set(v___x_3101_, 0, v___x_3103_);
v___x_3106_ = v___x_3101_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_nextMacroScope_3092_);
lean_ctor_set(v_reuseFailAlloc_3127_, 2, v_ngen_3093_);
lean_ctor_set(v_reuseFailAlloc_3127_, 3, v_auxDeclNGen_3094_);
lean_ctor_set(v_reuseFailAlloc_3127_, 4, v_traceState_3095_);
lean_ctor_set(v_reuseFailAlloc_3127_, 5, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3127_, 6, v_recordedDeps_3096_);
lean_ctor_set(v_reuseFailAlloc_3127_, 7, v_messages_3097_);
lean_ctor_set(v_reuseFailAlloc_3127_, 8, v_infoState_3098_);
lean_ctor_set(v_reuseFailAlloc_3127_, 9, v_snapshotTasks_3099_);
v___x_3106_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v_mctx_3109_; lean_object* v_zetaDeltaFVarIds_3110_; lean_object* v_postponed_3111_; lean_object* v_diag_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3125_; 
v___x_3107_ = lean_st_ref_put(v_a_3073_, v___x_3106_);
v___x_3108_ = lean_st_ref_take(v_a_3071_);
v_mctx_3109_ = lean_ctor_get(v___x_3108_, 0);
v_zetaDeltaFVarIds_3110_ = lean_ctor_get(v___x_3108_, 2);
v_postponed_3111_ = lean_ctor_get(v___x_3108_, 3);
v_diag_3112_ = lean_ctor_get(v___x_3108_, 4);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v___x_3108_, 1);
lean_dec(v_unused_3126_);
v___x_3114_ = v___x_3108_;
v_isShared_3115_ = v_isSharedCheck_3125_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_diag_3112_);
lean_inc(v_postponed_3111_);
lean_inc(v_zetaDeltaFVarIds_3110_);
lean_inc(v_mctx_3109_);
lean_dec(v___x_3108_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3125_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3116_ = lean_box(0);
v___x_3117_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 1, v___x_3117_);
v___x_3119_ = v___x_3114_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_mctx_3109_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_zetaDeltaFVarIds_3110_);
lean_ctor_set(v_reuseFailAlloc_3124_, 3, v_postponed_3111_);
lean_ctor_set(v_reuseFailAlloc_3124_, 4, v_diag_3112_);
v___x_3119_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3120_ = lean_st_ref_put(v_a_3071_, v___x_3119_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3116_);
v___x_3122_ = v___x_3087_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3116_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v_ext_3068_);
v_a_3131_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3084_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3084_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_3139_, lean_object* v_declName_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_3139_, v_declName_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
return v_res_3146_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3147_, lean_object* v_i_3148_, lean_object* v_k_3149_){
_start:
{
lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3150_ = lean_array_get_size(v_keys_3147_);
v___x_3151_ = lean_nat_dec_lt(v_i_3148_, v___x_3150_);
if (v___x_3151_ == 0)
{
lean_dec(v_i_3148_);
return v___x_3151_;
}
else
{
lean_object* v_k_x27_3152_; uint8_t v___x_3153_; 
v_k_x27_3152_ = lean_array_fget_borrowed(v_keys_3147_, v_i_3148_);
v___x_3153_ = lean_name_eq(v_k_3149_, v_k_x27_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_unsigned_to_nat(1u);
v___x_3155_ = lean_nat_add(v_i_3148_, v___x_3154_);
lean_dec(v_i_3148_);
v_i_3148_ = v___x_3155_;
goto _start;
}
else
{
lean_dec(v_i_3148_);
return v___x_3151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3157_, lean_object* v_i_3158_, lean_object* v_k_3159_){
_start:
{
uint8_t v_res_3160_; lean_object* v_r_3161_; 
v_res_3160_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_3157_, v_i_3158_, v_k_3159_);
lean_dec(v_k_3159_);
lean_dec_ref(v_keys_3157_);
v_r_3161_ = lean_box(v_res_3160_);
return v_r_3161_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_3162_, size_t v_x_3163_, lean_object* v_x_3164_){
_start:
{
if (lean_obj_tag(v_x_3162_) == 0)
{
lean_object* v_es_3165_; lean_object* v___x_3166_; size_t v___x_3167_; size_t v___x_3168_; lean_object* v_j_3169_; lean_object* v___x_3170_; 
v_es_3165_ = lean_ctor_get(v_x_3162_, 0);
v___x_3166_ = lean_box(2);
v___x_3167_ = ((size_t)31ULL);
v___x_3168_ = lean_usize_land(v_x_3163_, v___x_3167_);
v_j_3169_ = lean_usize_to_nat(v___x_3168_);
v___x_3170_ = lean_array_get_borrowed(v___x_3166_, v_es_3165_, v_j_3169_);
lean_dec(v_j_3169_);
switch(lean_obj_tag(v___x_3170_))
{
case 0:
{
lean_object* v_key_3171_; uint8_t v___x_3172_; 
v_key_3171_ = lean_ctor_get(v___x_3170_, 0);
v___x_3172_ = lean_name_eq(v_x_3164_, v_key_3171_);
return v___x_3172_;
}
case 1:
{
lean_object* v_node_3173_; size_t v___x_3174_; size_t v___x_3175_; 
v_node_3173_ = lean_ctor_get(v___x_3170_, 0);
v___x_3174_ = ((size_t)5ULL);
v___x_3175_ = lean_usize_shift_right(v_x_3163_, v___x_3174_);
v_x_3162_ = v_node_3173_;
v_x_3163_ = v___x_3175_;
goto _start;
}
default: 
{
uint8_t v___x_3177_; 
v___x_3177_ = 0;
return v___x_3177_;
}
}
}
else
{
lean_object* v_ks_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
v_ks_3178_ = lean_ctor_get(v_x_3162_, 0);
v___x_3179_ = lean_unsigned_to_nat(0u);
v___x_3180_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_3178_, v___x_3179_, v_x_3164_);
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_3181_, lean_object* v_x_3182_, lean_object* v_x_3183_){
_start:
{
size_t v_x_330__boxed_3184_; uint8_t v_res_3185_; lean_object* v_r_3186_; 
v_x_330__boxed_3184_ = lean_unbox_usize(v_x_3182_);
lean_dec(v_x_3182_);
v_res_3185_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3181_, v_x_330__boxed_3184_, v_x_3183_);
lean_dec(v_x_3183_);
lean_dec_ref(v_x_3181_);
v_r_3186_ = lean_box(v_res_3185_);
return v_r_3186_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_3187_, lean_object* v_x_3188_){
_start:
{
uint64_t v___y_3190_; 
if (lean_obj_tag(v_x_3188_) == 0)
{
uint64_t v___x_3193_; 
v___x_3193_ = 1723ULL;
v___y_3190_ = v___x_3193_;
goto v___jp_3189_;
}
else
{
uint64_t v_hash_3194_; 
v_hash_3194_ = lean_ctor_get_uint64(v_x_3188_, sizeof(void*)*2);
v___y_3190_ = v_hash_3194_;
goto v___jp_3189_;
}
v___jp_3189_:
{
size_t v___x_3191_; uint8_t v___x_3192_; 
v___x_3191_ = lean_uint64_to_usize(v___y_3190_);
v___x_3192_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3187_, v___x_3191_, v_x_3188_);
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_3195_, lean_object* v_x_3196_){
_start:
{
uint8_t v_res_3197_; lean_object* v_r_3198_; 
v_res_3197_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_3195_, v_x_3196_);
lean_dec(v_x_3196_);
lean_dec_ref(v_x_3195_);
v_r_3198_ = lean_box(v_res_3197_);
return v_r_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_3199_, lean_object* v_declName_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v_ext_3205_; lean_object* v_toEnvExtension_3206_; lean_object* v_env_3207_; lean_object* v_asyncMode_3208_; uint8_t v___x_3209_; lean_object* v___x_3210_; lean_object* v_extThms_3211_; uint8_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3203_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3204_ = lean_st_ref_get(v_a_3201_);
v_ext_3205_ = lean_ctor_get(v_ext_3199_, 1);
v_toEnvExtension_3206_ = lean_ctor_get(v_ext_3205_, 0);
v_env_3207_ = lean_ctor_get(v___x_3204_, 0);
lean_inc_ref(v_env_3207_);
lean_dec(v___x_3204_);
v_asyncMode_3208_ = lean_ctor_get(v_toEnvExtension_3206_, 2);
v___x_3209_ = 0;
v___x_3210_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3203_, v_ext_3199_, v_env_3207_, v_asyncMode_3208_, v___x_3209_);
v_extThms_3211_ = lean_ctor_get(v___x_3210_, 1);
lean_inc_ref(v_extThms_3211_);
lean_dec(v___x_3210_);
v___x_3212_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_3211_, v_declName_3200_);
lean_dec_ref(v_extThms_3211_);
v___x_3213_ = lean_box(v___x_3212_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_3215_, lean_object* v_declName_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3215_, v_declName_3216_, v_a_3217_);
lean_dec(v_a_3217_);
lean_dec(v_declName_3216_);
lean_dec_ref(v_ext_3215_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_3220_, lean_object* v_declName_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3220_, v_declName_3221_, v_a_3223_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_3226_, lean_object* v_declName_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_3226_, v_declName_3227_, v_a_3228_, v_a_3229_);
lean_dec(v_a_3229_);
lean_dec_ref(v_a_3228_);
lean_dec(v_declName_3227_);
lean_dec_ref(v_ext_3226_);
return v_res_3231_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_3232_, lean_object* v_x_3233_, lean_object* v_x_3234_){
_start:
{
uint8_t v___x_3235_; 
v___x_3235_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_3233_, v_x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_3236_, lean_object* v_x_3237_, lean_object* v_x_3238_){
_start:
{
uint8_t v_res_3239_; lean_object* v_r_3240_; 
v_res_3239_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_3236_, v_x_3237_, v_x_3238_);
lean_dec(v_x_3238_);
lean_dec_ref(v_x_3237_);
v_r_3240_ = lean_box(v_res_3239_);
return v_r_3240_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_3241_, lean_object* v_x_3242_, size_t v_x_3243_, lean_object* v_x_3244_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3242_, v_x_3243_, v_x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3246_, lean_object* v_x_3247_, lean_object* v_x_3248_, lean_object* v_x_3249_){
_start:
{
size_t v_x_417__boxed_3250_; uint8_t v_res_3251_; lean_object* v_r_3252_; 
v_x_417__boxed_3250_ = lean_unbox_usize(v_x_3248_);
lean_dec(v_x_3248_);
v_res_3251_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_3246_, v_x_3247_, v_x_417__boxed_3250_, v_x_3249_);
lean_dec(v_x_3249_);
lean_dec_ref(v_x_3247_);
v_r_3252_ = lean_box(v_res_3251_);
return v_r_3252_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3253_, lean_object* v_keys_3254_, lean_object* v_vals_3255_, lean_object* v_heq_3256_, lean_object* v_i_3257_, lean_object* v_k_3258_){
_start:
{
uint8_t v___x_3259_; 
v___x_3259_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_3254_, v_i_3257_, v_k_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3260_, lean_object* v_keys_3261_, lean_object* v_vals_3262_, lean_object* v_heq_3263_, lean_object* v_i_3264_, lean_object* v_k_3265_){
_start:
{
uint8_t v_res_3266_; lean_object* v_r_3267_; 
v_res_3266_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_3260_, v_keys_3261_, v_vals_3262_, v_heq_3263_, v_i_3264_, v_k_3265_);
lean_dec(v_k_3265_);
lean_dec_ref(v_vals_3262_);
lean_dec_ref(v_keys_3261_);
v_r_3267_ = lean_box(v_res_3266_);
return v_r_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_3268_, lean_object* v_declName_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v_ext_3274_; lean_object* v_toEnvExtension_3275_; lean_object* v_env_3276_; lean_object* v_asyncMode_3277_; uint8_t v___x_3278_; lean_object* v___x_3279_; lean_object* v_inj_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3272_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3273_ = lean_st_ref_get(v_a_3270_);
v_ext_3274_ = lean_ctor_get(v_ext_3268_, 1);
v_toEnvExtension_3275_ = lean_ctor_get(v_ext_3274_, 0);
v_env_3276_ = lean_ctor_get(v___x_3273_, 0);
lean_inc_ref(v_env_3276_);
lean_dec(v___x_3273_);
v_asyncMode_3277_ = lean_ctor_get(v_toEnvExtension_3275_, 2);
v___x_3278_ = 0;
v___x_3279_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3272_, v_ext_3268_, v_env_3276_, v_asyncMode_3277_, v___x_3278_);
v_inj_3280_ = lean_ctor_get(v___x_3279_, 4);
lean_inc_ref(v_inj_3280_);
lean_dec(v___x_3279_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_declName_3269_);
v___x_3282_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_3280_, v___x_3281_);
lean_dec_ref_known(v___x_3281_, 1);
lean_dec_ref(v_inj_3280_);
v___x_3283_ = lean_box(v___x_3282_);
v___x_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_3285_, lean_object* v_declName_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3285_, v_declName_3286_, v_a_3287_);
lean_dec(v_a_3287_);
lean_dec_ref(v_ext_3285_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_3290_, lean_object* v_declName_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3290_, v_declName_3291_, v_a_3293_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_3296_, lean_object* v_declName_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_3296_, v_declName_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec_ref(v_ext_3296_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_3302_, lean_object* v_declName_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v_ext_3308_; lean_object* v_toEnvExtension_3309_; lean_object* v_env_3310_; lean_object* v_asyncMode_3311_; uint8_t v___x_3312_; lean_object* v___x_3313_; lean_object* v_funCC_3314_; uint8_t v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3306_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3307_ = lean_st_ref_get(v_a_3304_);
v_ext_3308_ = lean_ctor_get(v_ext_3302_, 1);
v_toEnvExtension_3309_ = lean_ctor_get(v_ext_3308_, 0);
v_env_3310_ = lean_ctor_get(v___x_3307_, 0);
lean_inc_ref(v_env_3310_);
lean_dec(v___x_3307_);
v_asyncMode_3311_ = lean_ctor_get(v_toEnvExtension_3309_, 2);
v___x_3312_ = 0;
v___x_3313_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3306_, v_ext_3302_, v_env_3310_, v_asyncMode_3311_, v___x_3312_);
v_funCC_3314_ = lean_ctor_get(v___x_3313_, 2);
lean_inc(v_funCC_3314_);
lean_dec(v___x_3313_);
v___x_3315_ = l_Lean_NameSet_contains(v_funCC_3314_, v_declName_3303_);
lean_dec(v_funCC_3314_);
v___x_3316_ = lean_box(v___x_3315_);
v___x_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_3318_, lean_object* v_declName_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3318_, v_declName_3319_, v_a_3320_);
lean_dec(v_a_3320_);
lean_dec(v_declName_3319_);
lean_dec_ref(v_ext_3318_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_3323_, lean_object* v_declName_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3323_, v_declName_3324_, v_a_3326_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_3329_, lean_object* v_declName_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_3329_, v_declName_3330_, v_a_3331_, v_a_3332_);
lean_dec(v_a_3332_);
lean_dec_ref(v_a_3331_);
lean_dec(v_declName_3330_);
lean_dec_ref(v_ext_3329_);
return v_res_3334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_3359_ = l_Lean_mkAtom(v___x_3358_);
return v___x_3359_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_3361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3362_ = lean_array_push(v___x_3361_, v___x_3360_);
return v___x_3362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_3372_ = l_Lean_mkAtom(v___x_3371_);
return v___x_3372_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_3374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3375_ = lean_array_push(v___x_3374_, v___x_3373_);
return v___x_3375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_3377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_3378_ = lean_box(2);
v___x_3379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
lean_ctor_set(v___x_3379_, 1, v___x_3377_);
lean_ctor_set(v___x_3379_, 2, v___x_3376_);
return v___x_3379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3380_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_3381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_3382_ = lean_array_push(v___x_3381_, v___x_3380_);
return v___x_3382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3383_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_3384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_3385_ = lean_box(2);
v___x_3386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v___x_3384_);
lean_ctor_set(v___x_3386_, 2, v___x_3383_);
return v___x_3386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_3388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3389_ = lean_array_push(v___x_3388_, v___x_3387_);
return v___x_3389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3390_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_3391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_3392_ = lean_box(2);
v___x_3393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v___x_3391_);
lean_ctor_set(v___x_3393_, 2, v___x_3390_);
return v___x_3393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_3395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3396_ = lean_array_push(v___x_3395_, v___x_3394_);
return v___x_3396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3397_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_3398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_3399_ = lean_box(2);
v___x_3400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
lean_ctor_set(v___x_3400_, 1, v___x_3398_);
lean_ctor_set(v___x_3400_, 2, v___x_3397_);
return v___x_3400_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_3402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3403_ = lean_array_push(v___x_3402_, v___x_3401_);
return v___x_3403_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3404_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_3405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_3406_ = lean_box(2);
v___x_3407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
lean_ctor_set(v___x_3407_, 1, v___x_3405_);
lean_ctor_set(v___x_3407_, 2, v___x_3404_);
return v___x_3407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_3409_, lean_object* v_ext_3410_, lean_object* v_____r_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
uint8_t v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = 0;
lean_inc(v_declName_3409_);
v___x_3418_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_3409_, v___x_3417_, v___y_3414_, v___y_3415_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; uint8_t v___x_3420_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
v___x_3420_ = lean_unbox(v_a_3419_);
lean_dec(v_a_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v_a_3422_; uint8_t v___x_3423_; 
v___x_3421_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3410_, v_declName_3409_, v___y_3415_);
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = lean_unbox(v_a_3422_);
lean_dec(v_a_3422_);
if (v___x_3423_ == 0)
{
lean_object* v___x_3424_; lean_object* v_a_3425_; uint8_t v___x_3426_; 
lean_inc(v_declName_3409_);
v___x_3424_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3410_, v_declName_3409_, v___y_3415_);
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref(v___x_3424_);
v___x_3426_ = lean_unbox(v_a_3425_);
lean_dec(v_a_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; lean_object* v_a_3428_; uint8_t v___x_3429_; 
v___x_3427_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3410_, v_declName_3409_, v___y_3415_);
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref(v___x_3427_);
v___x_3429_ = lean_unbox(v_a_3428_);
lean_dec(v_a_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
v___x_3430_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_3410_, v_declName_3409_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v___x_3430_;
}
else
{
lean_object* v___x_3431_; 
v___x_3431_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_3410_, v_declName_3409_, v___y_3414_, v___y_3415_);
return v___x_3431_;
}
}
else
{
lean_object* v___x_3432_; 
v___x_3432_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_3410_, v_declName_3409_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v___x_3432_;
}
}
else
{
lean_object* v___x_3433_; 
v___x_3433_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_3410_, v_declName_3409_, v___y_3414_, v___y_3415_);
return v___x_3433_;
}
}
else
{
lean_object* v___x_3434_; 
v___x_3434_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_3410_, v_declName_3409_, v___y_3414_, v___y_3415_);
return v___x_3434_;
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec_ref(v_ext_3410_);
lean_dec(v_declName_3409_);
v_a_3435_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3418_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3418_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_3443_, lean_object* v_ext_3444_, lean_object* v_____r_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_3443_, v_ext_3444_, v_____r_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v_ref_3458_; lean_object* v___x_3459_; lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3468_; 
v_ref_3458_ = lean_ctor_get(v___y_3455_, 2);
v___x_3459_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msg_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3462_ = v___x_3459_;
v_isShared_3463_ = v_isSharedCheck_3468_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3468_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3466_; 
lean_inc(v_ref_3458_);
v___x_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3464_, 0, v_ref_3458_);
lean_ctor_set(v___x_3464_, 1, v_a_3460_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set_tag(v___x_3462_, 1);
lean_ctor_set(v___x_3462_, 0, v___x_3464_);
v___x_3466_ = v___x_3462_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
return v_res_3475_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3482_; uint64_t v___x_3483_; 
v___x_3482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_3483_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3482_);
return v___x_3483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_3485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_3486_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set_uint64(v___x_3486_, sizeof(void*)*1, v___x_3484_);
return v___x_3486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
return v___x_3488_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3489_ = lean_box(1);
v___x_3490_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_3491_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
lean_ctor_set(v___x_3492_, 1, v___x_3490_);
lean_ctor_set(v___x_3492_, 2, v___x_3489_);
return v___x_3492_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3495_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3496_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3497_ = lean_unsigned_to_nat(0u);
v___x_3498_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
lean_ctor_set(v___x_3498_, 2, v___x_3497_);
lean_ctor_set(v___x_3498_, 3, v___x_3497_);
lean_ctor_set(v___x_3498_, 4, v___x_3496_);
lean_ctor_set(v___x_3498_, 5, v___x_3496_);
lean_ctor_set(v___x_3498_, 6, v___x_3496_);
lean_ctor_set(v___x_3498_, 7, v___x_3496_);
lean_ctor_set(v___x_3498_, 8, v___x_3496_);
lean_ctor_set(v___x_3498_, 9, v___x_3496_);
lean_ctor_set(v___x_3498_, 10, v___x_3496_);
lean_ctor_set(v___x_3498_, 11, v___x_3495_);
return v___x_3498_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3500_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
lean_ctor_set(v___x_3500_, 2, v___x_3499_);
lean_ctor_set(v___x_3500_, 3, v___x_3499_);
lean_ctor_set(v___x_3500_, 4, v___x_3499_);
lean_ctor_set(v___x_3500_, 5, v___x_3499_);
lean_ctor_set(v___x_3500_, 6, v___x_3499_);
return v___x_3500_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
lean_ctor_set(v___x_3502_, 2, v___x_3501_);
lean_ctor_set(v___x_3502_, 3, v___x_3501_);
lean_ctor_set(v___x_3502_, 4, v___x_3501_);
return v___x_3502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9));
v___x_3505_ = l_Lean_stringToMessageData(v___x_3504_);
return v___x_3505_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11));
v___x_3508_ = l_Lean_stringToMessageData(v___x_3507_);
return v___x_3508_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13));
v___x_3511_ = l_Lean_stringToMessageData(v___x_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v_ext_3512_, lean_object* v___x_3513_, uint8_t v_showInfo_3514_, lean_object* v_attrName_3515_, lean_object* v_declName_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
uint8_t v___x_3520_; uint8_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___y_3535_; 
v___x_3520_ = 1;
v___x_3521_ = 0;
v___x_3522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3523_ = lean_unsigned_to_nat(0u);
v___x_3524_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_3525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_3526_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_3527_ = lean_box(0);
lean_inc(v___x_3513_);
v___x_3528_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3528_, 0, v___x_3522_);
lean_ctor_set(v___x_3528_, 1, v___x_3513_);
lean_ctor_set(v___x_3528_, 2, v___x_3525_);
lean_ctor_set(v___x_3528_, 3, v___x_3526_);
lean_ctor_set(v___x_3528_, 4, v___x_3527_);
lean_ctor_set(v___x_3528_, 5, v___x_3523_);
lean_ctor_set(v___x_3528_, 6, v___x_3527_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*7, v___x_3521_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*7 + 1, v___x_3521_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*7 + 2, v___x_3521_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*7 + 3, v___x_3520_);
v___x_3529_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_3530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3529_);
lean_ctor_set(v___x_3532_, 1, v___x_3530_);
lean_ctor_set(v___x_3532_, 2, v___x_3513_);
lean_ctor_set(v___x_3532_, 3, v___x_3524_);
lean_ctor_set(v___x_3532_, 4, v___x_3531_);
v___x_3533_ = lean_st_mk_ref(v___x_3532_);
if (v_showInfo_3514_ == 0)
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec(v_attrName_3515_);
v___x_3545_ = lean_box(0);
v___x_3546_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_3516_, v_ext_3512_, v___x_3545_, v___x_3528_, v___x_3533_, v___y_3517_, v___y_3518_);
lean_dec_ref_known(v___x_3528_, 7);
v___y_3535_ = v___x_3546_;
goto v___jp_3534_;
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
lean_dec(v_declName_3516_);
lean_dec_ref(v_ext_3512_);
v___x_3547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_3548_ = l_Lean_MessageData_ofName(v_attrName_3515_);
lean_inc_ref(v___x_3548_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
lean_ctor_set(v___x_3552_, 1, v___x_3548_);
v___x_3553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14);
v___x_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3552_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3554_, v___x_3528_, v___x_3533_, v___y_3517_, v___y_3518_);
lean_dec(v___x_3533_);
lean_dec_ref_known(v___x_3528_, 7);
return v___x_3555_;
}
v___jp_3534_:
{
if (lean_obj_tag(v___y_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3544_; 
v_a_3536_ = lean_ctor_get(v___y_3535_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___y_3535_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3538_ = v___y_3535_;
v_isShared_3539_ = v_isSharedCheck_3544_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___y_3535_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3544_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v___x_3542_; 
v___x_3540_ = lean_st_ref_get(v___x_3533_);
lean_dec(v___x_3533_);
lean_dec(v___x_3540_);
if (v_isShared_3539_ == 0)
{
v___x_3542_ = v___x_3538_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3536_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
else
{
lean_dec(v___x_3533_);
return v___y_3535_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v_ext_3556_, lean_object* v___x_3557_, lean_object* v_showInfo_3558_, lean_object* v_attrName_3559_, lean_object* v_declName_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
uint8_t v_showInfo_boxed_3564_; lean_object* v_res_3565_; 
v_showInfo_boxed_3564_ = lean_unbox(v_showInfo_3558_);
v_res_3565_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v_ext_3556_, v___x_3557_, v_showInfo_boxed_3564_, v_attrName_3559_, v_declName_3560_, v___y_3561_, v___y_3562_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_3568_, uint8_t v_attrKind_3569_, uint8_t v_showInfo_3570_, uint8_t v_minIndexable_3571_, lean_object* v_as_x27_3572_, lean_object* v_b_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
if (lean_obj_tag(v_as_x27_3572_) == 0)
{
lean_object* v___x_3579_; 
lean_dec_ref(v_ext_3568_);
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v_b_3573_);
return v___x_3579_;
}
else
{
lean_object* v_head_3580_; lean_object* v_tail_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v_head_3580_ = lean_ctor_get(v_as_x27_3572_, 0);
v_tail_3581_ = lean_ctor_get(v_as_x27_3572_, 1);
v___x_3582_ = lean_box(0);
v___x_3583_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3577_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___x_3583_, 1);
v___x_3585_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_3580_);
lean_inc_ref(v_ext_3568_);
v___x_3586_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_3568_, v_head_3580_, v_attrKind_3569_, v___x_3585_, v_a_3584_, v_showInfo_3570_, v_minIndexable_3571_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_dec_ref_known(v___x_3586_, 1);
v_as_x27_3572_ = v_tail_3581_;
v_b_3573_ = v___x_3582_;
goto _start;
}
else
{
lean_dec_ref(v_ext_3568_);
return v___x_3586_;
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v_ext_3568_);
v_a_3588_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3583_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3583_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_3596_, lean_object* v_attrKind_3597_, lean_object* v_showInfo_3598_, lean_object* v_minIndexable_3599_, lean_object* v_as_x27_3600_, lean_object* v_b_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
uint8_t v_attrKind_boxed_3607_; uint8_t v_showInfo_boxed_3608_; uint8_t v_minIndexable_boxed_3609_; lean_object* v_res_3610_; 
v_attrKind_boxed_3607_ = lean_unbox(v_attrKind_3597_);
v_showInfo_boxed_3608_ = lean_unbox(v_showInfo_3598_);
v_minIndexable_boxed_3609_ = lean_unbox(v_minIndexable_3599_);
v_res_3610_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3596_, v_attrKind_boxed_3607_, v_showInfo_boxed_3608_, v_minIndexable_boxed_3609_, v_as_x27_3600_, v_b_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v_as_x27_3600_);
return v_res_3610_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_3613_ = l_Lean_stringToMessageData(v___x_3612_);
return v___x_3613_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_3616_ = l_Lean_stringToMessageData(v___x_3615_);
return v___x_3616_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_3619_ = l_Lean_stringToMessageData(v___x_3618_);
return v___x_3619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_3622_ = l_Lean_stringToMessageData(v___x_3621_);
return v___x_3622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_3627_ = l_Lean_stringToMessageData(v___x_3626_);
return v___x_3627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_3630_ = l_Lean_stringToMessageData(v___x_3629_);
return v___x_3630_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13));
v___x_3633_ = l_Lean_stringToMessageData(v___x_3632_);
return v___x_3633_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15));
v___x_3636_ = l_Lean_stringToMessageData(v___x_3635_);
return v___x_3636_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17));
v___x_3639_ = l_Lean_stringToMessageData(v___x_3638_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_declName_3640_, uint8_t v_attrKind_3641_, lean_object* v_stx_3642_, lean_object* v_ext_3643_, uint8_t v_showInfo_3644_, uint8_t v_minIndexable_3645_, uint8_t v___x_3646_, lean_object* v_attrName_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_3642_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_a_3676_);
lean_dec_ref_known(v___x_3675_, 1);
switch(lean_obj_tag(v_a_3676_))
{
case 0:
{
lean_object* v_k_3677_; 
lean_dec(v_attrName_3647_);
lean_dec(v_stx_3642_);
v_k_3677_ = lean_ctor_get(v_a_3676_, 0);
lean_inc(v_k_3677_);
lean_dec_ref_known(v_a_3676_, 1);
if (lean_obj_tag(v_k_3677_) == 9)
{
lean_object* v___x_3678_; 
lean_dec_ref(v_ext_3643_);
lean_dec(v_declName_3640_);
v___x_3678_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_3650_, v___y_3651_);
return v___x_3678_;
}
else
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3651_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3681_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v___x_3679_, 1);
v___x_3681_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_3643_, v_declName_3640_, v_attrKind_3641_, v_k_3677_, v_a_3680_, v_showInfo_3644_, v_minIndexable_3645_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3681_;
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec(v_k_3677_);
lean_dec_ref(v_ext_3643_);
lean_dec(v_declName_3640_);
v_a_3682_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3679_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3679_);
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
case 1:
{
uint8_t v_eager_3690_; lean_object* v___x_3691_; 
lean_dec(v_attrName_3647_);
lean_dec(v_stx_3642_);
v_eager_3690_ = lean_ctor_get_uint8(v_a_3676_, 0);
lean_dec_ref_known(v_a_3676_, 0);
v___x_3691_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_3643_, v_declName_3640_, v_eager_3690_, v_attrKind_3641_, v___y_3650_, v___y_3651_);
return v___x_3691_;
}
case 2:
{
lean_object* v___x_3692_; 
lean_dec(v_stx_3642_);
lean_inc(v_declName_3640_);
v___x_3692_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_3640_, v___x_3646_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
if (lean_obj_tag(v_a_3693_) == 1)
{
lean_object* v_val_3694_; lean_object* v_ctors_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_dec(v_attrName_3647_);
lean_dec(v_declName_3640_);
v_val_3694_ = lean_ctor_get(v_a_3693_, 0);
lean_inc(v_val_3694_);
lean_dec_ref_known(v_a_3693_, 1);
v_ctors_3695_ = lean_ctor_get(v_val_3694_, 4);
lean_inc(v_ctors_3695_);
lean_dec(v_val_3694_);
v___x_3696_ = lean_box(0);
v___x_3697_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3643_, v_attrKind_3641_, v_showInfo_3644_, v_minIndexable_3645_, v_ctors_3695_, v___x_3696_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v_ctors_3695_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3704_ == 0)
{
lean_object* v_unused_3705_; 
v_unused_3705_ = lean_ctor_get(v___x_3697_, 0);
lean_dec(v_unused_3705_);
v___x_3699_ = v___x_3697_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_dec(v___x_3697_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3696_);
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3696_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
else
{
return v___x_3697_;
}
}
else
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
lean_dec(v_a_3693_);
lean_dec_ref(v_ext_3643_);
v___x_3706_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_3707_ = l_Lean_MessageData_ofName(v_attrName_3647_);
v___x_3708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3706_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3708_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = l_Lean_MessageData_ofConstName(v_declName_3640_, v___x_3646_);
v___x_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3714_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3715_;
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v_attrName_3647_);
lean_dec_ref(v_ext_3643_);
lean_dec(v_declName_3640_);
v_a_3716_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3692_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3692_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
case 3:
{
lean_object* v___x_3724_; 
lean_dec(v_attrName_3647_);
lean_inc(v_declName_3640_);
v___x_3724_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_3640_, v___x_3646_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___x_3724_, 1);
if (lean_obj_tag(v_a_3725_) == 1)
{
lean_object* v_val_3726_; lean_object* v___x_3727_; 
lean_dec(v_stx_3642_);
lean_dec(v_declName_3640_);
v_val_3726_ = lean_ctor_get(v_a_3725_, 0);
lean_inc_n(v_val_3726_, 2);
lean_dec_ref_known(v_a_3725_, 1);
lean_inc_ref(v_ext_3643_);
v___x_3727_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_3643_, v_val_3726_, v___x_3646_, v_attrKind_3641_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v___x_3728_; 
lean_dec_ref_known(v___x_3727_, 1);
v___x_3728_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3726_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3749_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3731_ = v___x_3728_;
v_isShared_3732_ = v_isSharedCheck_3749_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3728_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3749_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
if (lean_obj_tag(v_a_3729_) == 1)
{
lean_object* v_val_3733_; lean_object* v_ctors_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
lean_del_object(v___x_3731_);
v_val_3733_ = lean_ctor_get(v_a_3729_, 0);
lean_inc(v_val_3733_);
lean_dec_ref_known(v_a_3729_, 1);
v_ctors_3734_ = lean_ctor_get(v_val_3733_, 4);
lean_inc(v_ctors_3734_);
lean_dec(v_val_3733_);
v___x_3735_ = lean_box(0);
v___x_3736_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3643_, v_attrKind_3641_, v_showInfo_3644_, v_minIndexable_3645_, v_ctors_3734_, v___x_3735_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v_ctors_3734_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3743_ == 0)
{
lean_object* v_unused_3744_; 
v_unused_3744_ = lean_ctor_get(v___x_3736_, 0);
lean_dec(v_unused_3744_);
v___x_3738_ = v___x_3736_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_dec(v___x_3736_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 0, v___x_3735_);
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3735_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
else
{
return v___x_3736_;
}
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_dec(v_a_3729_);
lean_dec_ref(v_ext_3643_);
v___x_3745_ = lean_box(0);
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 0, v___x_3745_);
v___x_3747_ = v___x_3731_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec_ref(v_ext_3643_);
v_a_3750_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3728_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3728_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
else
{
lean_dec(v_val_3726_);
lean_dec_ref(v_ext_3643_);
return v___x_3727_;
}
}
else
{
lean_object* v___x_3758_; 
lean_dec(v_a_3725_);
v___x_3758_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3651_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3760_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref_known(v___x_3758_, 1);
v___x_3760_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_3643_, v_stx_3642_, v_declName_3640_, v_attrKind_3641_, v_a_3759_, v_minIndexable_3645_, v_showInfo_3644_, v___x_3646_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3760_;
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec_ref(v_ext_3643_);
lean_dec(v_stx_3642_);
lean_dec(v_declName_3640_);
v_a_3761_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3758_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3758_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec_ref(v_ext_3643_);
lean_dec(v_stx_3642_);
lean_dec(v_declName_3640_);
v_a_3769_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3724_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3724_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
case 4:
{
lean_object* v___x_3777_; 
lean_dec(v_attrName_3647_);
lean_dec(v_stx_3642_);
v___x_3777_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_3643_, v_declName_3640_, v_attrKind_3641_, v___y_3650_, v___y_3651_);
return v___x_3777_;
}
case 5:
{
lean_object* v_prio_3778_; lean_object* v___x_3779_; uint8_t v___x_3780_; 
lean_dec_ref(v_ext_3643_);
lean_dec(v_stx_3642_);
v_prio_3778_ = lean_ctor_get(v_a_3676_, 0);
lean_inc(v_prio_3778_);
lean_dec_ref_known(v_a_3676_, 1);
v___x_3779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3780_ = lean_name_eq(v_attrName_3647_, v___x_3779_);
lean_dec(v_attrName_3647_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
lean_dec(v_prio_3778_);
lean_dec(v_declName_3640_);
v___x_3781_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10);
v___x_3782_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3781_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3782_;
}
else
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_3640_, v_attrKind_3641_, v_prio_3778_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3783_;
}
}
case 6:
{
lean_object* v___x_3784_; 
lean_dec(v_attrName_3647_);
lean_dec(v_stx_3642_);
v___x_3784_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_3643_, v_declName_3640_, v_attrKind_3641_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3784_;
}
case 7:
{
lean_object* v___x_3785_; 
lean_dec(v_attrName_3647_);
lean_dec(v_stx_3642_);
v___x_3785_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_3643_, v_declName_3640_, v_attrKind_3641_, v___y_3650_, v___y_3651_);
return v___x_3785_;
}
case 8:
{
uint8_t v_post_3786_; uint8_t v_inv_3787_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___x_3795_; uint8_t v___x_3796_; 
lean_dec_ref(v_ext_3643_);
lean_dec(v_stx_3642_);
v_post_3786_ = lean_ctor_get_uint8(v_a_3676_, 0);
v_inv_3787_ = lean_ctor_get_uint8(v_a_3676_, 1);
lean_dec_ref_known(v_a_3676_, 0);
v___x_3795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3796_ = lean_name_eq(v_attrName_3647_, v___x_3795_);
lean_dec(v_attrName_3647_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_dec(v_declName_3640_);
v___x_3797_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12);
v___x_3798_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3797_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3798_;
}
else
{
v___y_3789_ = v___y_3648_;
v___y_3790_ = v___y_3649_;
v___y_3791_ = v___y_3650_;
v___y_3792_ = v___y_3651_;
goto v___jp_3788_;
}
v___jp_3788_:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3793_ = lean_unsigned_to_nat(1000u);
v___x_3794_ = l_Lean_Meta_Grind_addNormTheorem(v_declName_3640_, v_post_3786_, v_inv_3787_, v_attrKind_3641_, v___x_3793_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
return v___x_3794_;
}
}
case 9:
{
lean_object* v___x_3799_; uint8_t v___x_3800_; 
lean_dec_ref(v_ext_3643_);
lean_dec(v_stx_3642_);
v___x_3799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3800_ = lean_name_eq(v_attrName_3647_, v___x_3799_);
lean_dec(v_attrName_3647_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_dec(v_declName_3640_);
v___x_3801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14);
v___x_3802_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3801_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3802_;
}
else
{
goto v___jp_3653_;
}
}
case 10:
{
uint8_t v_fallback_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; 
lean_dec_ref(v_ext_3643_);
lean_dec(v_stx_3642_);
v_fallback_3803_ = lean_ctor_get_uint8(v_a_3676_, 0);
lean_dec_ref_known(v_a_3676_, 0);
v___x_3804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3805_ = lean_name_eq(v_attrName_3647_, v___x_3804_);
lean_dec(v_attrName_3647_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
lean_dec(v_declName_3640_);
v___x_3806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16);
v___x_3807_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3806_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3807_;
}
else
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_3640_, v_attrKind_3641_, v_fallback_3803_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3808_;
}
}
default: 
{
lean_object* v___x_3809_; uint8_t v___x_3810_; 
lean_dec_ref(v_ext_3643_);
lean_dec(v_stx_3642_);
v___x_3809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3810_ = lean_name_eq(v_attrName_3647_, v___x_3809_);
lean_dec(v_attrName_3647_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_dec(v_declName_3640_);
v___x_3811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18);
v___x_3812_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3811_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3812_;
}
else
{
lean_object* v___x_3813_; 
v___x_3813_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_3640_, v_attrKind_3641_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3813_;
}
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v_attrName_3647_);
lean_dec_ref(v_ext_3643_);
lean_dec(v_stx_3642_);
lean_dec(v_declName_3640_);
v_a_3814_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3675_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3675_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
v___jp_3653_:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_Meta_Grind_addNormDeclToUnfold(v_declName_3640_, v_attrKind_3641_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3666_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3666_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3666_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
uint8_t v___x_3659_; 
v___x_3659_ = lean_unbox(v_a_3655_);
lean_dec(v_a_3655_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
lean_del_object(v___x_3657_);
v___x_3660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_3661_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3660_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3661_;
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
v___x_3662_ = lean_box(0);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v___x_3662_);
v___x_3664_ = v___x_3657_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
v_a_3667_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3654_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3654_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_declName_3822_, lean_object* v_attrKind_3823_, lean_object* v_stx_3824_, lean_object* v_ext_3825_, lean_object* v_showInfo_3826_, lean_object* v_minIndexable_3827_, lean_object* v___x_3828_, lean_object* v_attrName_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
uint8_t v_attrKind_boxed_3835_; uint8_t v_showInfo_boxed_3836_; uint8_t v_minIndexable_boxed_3837_; uint8_t v___x_11429__boxed_3838_; lean_object* v_res_3839_; 
v_attrKind_boxed_3835_ = lean_unbox(v_attrKind_3823_);
v_showInfo_boxed_3836_ = lean_unbox(v_showInfo_3826_);
v_minIndexable_boxed_3837_ = lean_unbox(v_minIndexable_3827_);
v___x_11429__boxed_3838_ = lean_unbox(v___x_3828_);
v_res_3839_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_declName_3822_, v_attrKind_boxed_3835_, v_stx_3824_, v_ext_3825_, v_showInfo_boxed_3836_, v_minIndexable_boxed_3837_, v___x_11429__boxed_3838_, v_attrName_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0(lean_object* v___x_3840_, lean_object* v_entry_3841_, lean_object* v_s_3842_){
_start:
{
lean_object* v_addEntryFn_3843_; lean_object* v_importedEntries_3844_; lean_object* v_state_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3853_; 
v_addEntryFn_3843_ = lean_ctor_get(v___x_3840_, 3);
lean_inc(v_addEntryFn_3843_);
lean_dec_ref(v___x_3840_);
v_importedEntries_3844_ = lean_ctor_get(v_s_3842_, 0);
v_state_3845_ = lean_ctor_get(v_s_3842_, 1);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_s_3842_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3847_ = v_s_3842_;
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_state_3845_);
lean_inc(v_importedEntries_3844_);
lean_dec(v_s_3842_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v_state_3849_; lean_object* v___x_3851_; 
v_state_3849_ = lean_apply_2(v_addEntryFn_3843_, v_state_3845_, v_entry_3841_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 1, v_state_3849_);
v___x_3851_ = v___x_3847_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_importedEntries_3844_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_state_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_keys_3854_, lean_object* v_i_3855_, lean_object* v_k_3856_){
_start:
{
lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___x_3857_ = lean_array_get_size(v_keys_3854_);
v___x_3858_ = lean_nat_dec_lt(v_i_3855_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_dec(v_i_3855_);
return v___x_3858_;
}
else
{
lean_object* v_k_x27_3859_; uint8_t v___x_3860_; 
v_k_x27_3859_ = lean_array_fget_borrowed(v_keys_3854_, v_i_3855_);
v___x_3860_ = l_Lean_instBEqExtraModUse_beq(v_k_3856_, v_k_x27_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_unsigned_to_nat(1u);
v___x_3862_ = lean_nat_add(v_i_3855_, v___x_3861_);
lean_dec(v_i_3855_);
v_i_3855_ = v___x_3862_;
goto _start;
}
else
{
lean_dec(v_i_3855_);
return v___x_3858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_keys_3864_, lean_object* v_i_3865_, lean_object* v_k_3866_){
_start:
{
uint8_t v_res_3867_; lean_object* v_r_3868_; 
v_res_3867_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_keys_3864_, v_i_3865_, v_k_3866_);
lean_dec_ref(v_k_3866_);
lean_dec_ref(v_keys_3864_);
v_r_3868_ = lean_box(v_res_3867_);
return v_r_3868_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3869_, size_t v_x_3870_, lean_object* v_x_3871_){
_start:
{
if (lean_obj_tag(v_x_3869_) == 0)
{
lean_object* v_es_3872_; lean_object* v___x_3873_; size_t v___x_3874_; size_t v___x_3875_; lean_object* v_j_3876_; lean_object* v___x_3877_; 
v_es_3872_ = lean_ctor_get(v_x_3869_, 0);
v___x_3873_ = lean_box(2);
v___x_3874_ = ((size_t)31ULL);
v___x_3875_ = lean_usize_land(v_x_3870_, v___x_3874_);
v_j_3876_ = lean_usize_to_nat(v___x_3875_);
v___x_3877_ = lean_array_get_borrowed(v___x_3873_, v_es_3872_, v_j_3876_);
lean_dec(v_j_3876_);
switch(lean_obj_tag(v___x_3877_))
{
case 0:
{
lean_object* v_key_3878_; uint8_t v___x_3879_; 
v_key_3878_ = lean_ctor_get(v___x_3877_, 0);
v___x_3879_ = l_Lean_instBEqExtraModUse_beq(v_x_3871_, v_key_3878_);
return v___x_3879_;
}
case 1:
{
lean_object* v_node_3880_; size_t v___x_3881_; size_t v___x_3882_; 
v_node_3880_ = lean_ctor_get(v___x_3877_, 0);
v___x_3881_ = ((size_t)5ULL);
v___x_3882_ = lean_usize_shift_right(v_x_3870_, v___x_3881_);
v_x_3869_ = v_node_3880_;
v_x_3870_ = v___x_3882_;
goto _start;
}
default: 
{
uint8_t v___x_3884_; 
v___x_3884_ = 0;
return v___x_3884_;
}
}
}
else
{
lean_object* v_ks_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
v_ks_3885_ = lean_ctor_get(v_x_3869_, 0);
v___x_3886_ = lean_unsigned_to_nat(0u);
v___x_3887_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_ks_3885_, v___x_3886_, v_x_3871_);
return v___x_3887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_x_3888_, lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
size_t v_x_11855__boxed_3891_; uint8_t v_res_3892_; lean_object* v_r_3893_; 
v_x_11855__boxed_3891_ = lean_unbox_usize(v_x_3889_);
lean_dec(v_x_3889_);
v_res_3892_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_3888_, v_x_11855__boxed_3891_, v_x_3890_);
lean_dec_ref(v_x_3890_);
lean_dec_ref(v_x_3888_);
v_r_3893_ = lean_box(v_res_3892_);
return v_r_3893_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3894_, lean_object* v_x_3895_){
_start:
{
uint64_t v___x_3896_; size_t v___x_3897_; uint8_t v___x_3898_; 
v___x_3896_ = l_Lean_instHashableExtraModUse_hash(v_x_3895_);
v___x_3897_ = lean_uint64_to_usize(v___x_3896_);
v___x_3898_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_3894_, v___x_3897_, v_x_3895_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3899_, lean_object* v_x_3900_){
_start:
{
uint8_t v_res_3901_; lean_object* v_r_3902_; 
v_res_3901_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v_x_3899_, v_x_3900_);
lean_dec_ref(v_x_3900_);
lean_dec_ref(v_x_3899_);
v_r_3902_ = lean_box(v_res_3901_);
return v_r_3902_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_3903_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3));
v___x_3909_ = l_Lean_stringToMessageData(v___x_3908_);
return v___x_3909_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5));
v___x_3912_ = l_Lean_stringToMessageData(v___x_3911_);
return v___x_3912_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_3914_ = l_Lean_stringToMessageData(v___x_3913_);
return v___x_3914_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v_cls_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v_cls_3915_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_3916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1));
v___x_3917_ = l_Lean_Name_append(v___x_3916_, v_cls_3915_);
return v___x_3917_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9));
v___x_3920_ = l_Lean_stringToMessageData(v___x_3919_);
return v___x_3920_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12(void){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11));
v___x_3923_ = l_Lean_stringToMessageData(v___x_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(lean_object* v_mod_3928_, uint8_t v_isMeta_3929_, lean_object* v_hint_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v_env_3970_; uint8_t v_isExporting_3971_; lean_object* v_entry_3972_; lean_object* v___x_3973_; lean_object* v_env_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3968_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0);
v___x_3969_ = lean_st_ref_get(v___y_3934_);
v_env_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc_ref(v_env_3970_);
lean_dec(v___x_3969_);
v_isExporting_3971_ = lean_ctor_get_uint8(v_env_3970_, sizeof(void*)*13);
lean_dec_ref(v_env_3970_);
lean_inc(v_mod_3928_);
v_entry_3972_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3972_, 0, v_mod_3928_);
lean_ctor_set_uint8(v_entry_3972_, sizeof(void*)*1, v_isExporting_3971_);
lean_ctor_set_uint8(v_entry_3972_, sizeof(void*)*1 + 1, v_isMeta_3929_);
v___x_3973_ = lean_st_ref_get(v___y_3934_);
v_env_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc_ref(v_env_3974_);
lean_dec(v___x_3973_);
v___x_3975_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3976_ = lean_box(1);
v___x_3977_ = lean_box(0);
v___x_3978_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3968_, v___x_3975_, v_env_3974_, v___x_3976_, v___x_3977_);
v___x_3979_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v___x_3978_, v_entry_3972_);
lean_dec(v___x_3978_);
if (v___x_3979_ == 0)
{
lean_object* v_toCold_3980_; lean_object* v_options_3981_; lean_object* v_inheritedTraceOptions_3982_; uint8_t v_hasTrace_3983_; lean_object* v___f_3984_; uint8_t v___x_3985_; lean_object* v___y_3987_; lean_object* v___y_3988_; 
v_toCold_3980_ = lean_ctor_get(v___y_3933_, 0);
v_options_3981_ = lean_ctor_get(v_toCold_3980_, 2);
v_inheritedTraceOptions_3982_ = lean_ctor_get(v_toCold_3980_, 11);
v_hasTrace_3983_ = lean_ctor_get_uint8(v_options_3981_, sizeof(void*)*1);
v___f_3984_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_3984_, 0, v___x_3975_);
lean_closure_set(v___f_3984_, 1, v_entry_3972_);
v___x_3985_ = 1;
if (v_hasTrace_3983_ == 0)
{
lean_dec(v_hint_3930_);
lean_dec(v_mod_3928_);
v___y_3987_ = v___y_3932_;
v___y_3988_ = v___y_3934_;
goto v___jp_3986_;
}
else
{
lean_object* v_cls_4015_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v_cls_4015_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_4035_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8);
v___x_4036_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3982_, v_options_3981_, v___x_4035_);
if (v___x_4036_ == 0)
{
lean_dec(v_hint_3930_);
lean_dec(v_mod_3928_);
v___y_3987_ = v___y_3932_;
v___y_3988_ = v___y_3934_;
goto v___jp_3986_;
}
else
{
lean_object* v___x_4037_; lean_object* v___y_4039_; 
v___x_4037_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10);
if (v_isExporting_3971_ == 0)
{
lean_object* v___x_4046_; 
v___x_4046_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15));
v___y_4039_ = v___x_4046_;
goto v___jp_4038_;
}
else
{
lean_object* v___x_4047_; 
v___x_4047_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16));
v___y_4039_ = v___x_4047_;
goto v___jp_4038_;
}
v___jp_4038_:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
lean_inc_ref(v___y_4039_);
v___x_4040_ = l_Lean_stringToMessageData(v___y_4039_);
v___x_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4037_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___x_4042_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12);
v___x_4043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4041_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
if (v_isMeta_3929_ == 0)
{
lean_object* v___x_4044_; 
v___x_4044_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13));
v___y_4022_ = v___x_4043_;
v___y_4023_ = v___x_4044_;
goto v___jp_4021_;
}
else
{
lean_object* v___x_4045_; 
v___x_4045_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14));
v___y_4022_ = v___x_4043_;
v___y_4023_ = v___x_4045_;
goto v___jp_4021_;
}
}
}
v___jp_4016_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___y_4017_);
lean_ctor_set(v___x_4019_, 1, v___y_4018_);
v___x_4020_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_4015_, v___x_4019_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_dec_ref_known(v___x_4020_, 1);
v___y_3987_ = v___y_3932_;
v___y_3988_ = v___y_3934_;
goto v___jp_3986_;
}
else
{
lean_dec_ref(v___f_3984_);
return v___x_4020_;
}
}
v___jp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; 
lean_inc_ref(v___y_4023_);
v___x_4024_ = l_Lean_stringToMessageData(v___y_4023_);
v___x_4025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___y_4022_);
lean_ctor_set(v___x_4025_, 1, v___x_4024_);
v___x_4026_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4);
v___x_4027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4025_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = l_Lean_MessageData_ofName(v_mod_3928_);
v___x_4029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4027_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = l_Lean_Name_isAnonymous(v_hint_3930_);
if (v___x_4030_ == 0)
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4031_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6);
v___x_4032_ = l_Lean_MessageData_ofName(v_hint_3930_);
v___x_4033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4031_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
v___y_4017_ = v___x_4029_;
v___y_4018_ = v___x_4033_;
goto v___jp_4016_;
}
else
{
lean_object* v___x_4034_; 
lean_dec(v_hint_3930_);
v___x_4034_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7);
v___y_4017_ = v___x_4029_;
v___y_4018_ = v___x_4034_;
goto v___jp_4016_;
}
}
}
v___jp_3986_:
{
lean_object* v___x_3989_; lean_object* v_toEnvExtension_3990_; uint8_t v_logWrites_3991_; 
v___x_3989_ = lean_st_ref_take(v___y_3988_);
v_toEnvExtension_3990_ = lean_ctor_get(v___x_3975_, 0);
v_logWrites_3991_ = lean_ctor_get_uint8(v_toEnvExtension_3990_, sizeof(void*)*6);
if (v_logWrites_3991_ == 0)
{
lean_object* v_env_3992_; lean_object* v_nextMacroScope_3993_; lean_object* v_ngen_3994_; lean_object* v_auxDeclNGen_3995_; lean_object* v_traceState_3996_; lean_object* v_recordedDeps_3997_; lean_object* v_messages_3998_; lean_object* v_infoState_3999_; lean_object* v_snapshotTasks_4000_; lean_object* v_asyncMode_4001_; lean_object* v___x_4002_; 
v_env_3992_ = lean_ctor_get(v___x_3989_, 0);
lean_inc_ref(v_env_3992_);
v_nextMacroScope_3993_ = lean_ctor_get(v___x_3989_, 1);
lean_inc(v_nextMacroScope_3993_);
v_ngen_3994_ = lean_ctor_get(v___x_3989_, 2);
lean_inc_ref(v_ngen_3994_);
v_auxDeclNGen_3995_ = lean_ctor_get(v___x_3989_, 3);
lean_inc_ref(v_auxDeclNGen_3995_);
v_traceState_3996_ = lean_ctor_get(v___x_3989_, 4);
lean_inc_ref(v_traceState_3996_);
v_recordedDeps_3997_ = lean_ctor_get(v___x_3989_, 6);
lean_inc_ref(v_recordedDeps_3997_);
v_messages_3998_ = lean_ctor_get(v___x_3989_, 7);
lean_inc_ref(v_messages_3998_);
v_infoState_3999_ = lean_ctor_get(v___x_3989_, 8);
lean_inc_ref(v_infoState_3999_);
v_snapshotTasks_4000_ = lean_ctor_get(v___x_3989_, 9);
lean_inc_ref(v_snapshotTasks_4000_);
lean_dec(v___x_3989_);
v_asyncMode_4001_ = lean_ctor_get(v_toEnvExtension_3990_, 2);
lean_inc_ref(v_toEnvExtension_3990_);
v___x_4002_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3990_, v_env_3992_, v___f_3984_, v_asyncMode_4001_, v___x_3977_, v___x_3985_);
v___y_3937_ = v_ngen_3994_;
v___y_3938_ = v___y_3987_;
v___y_3939_ = v_snapshotTasks_4000_;
v___y_3940_ = v_messages_3998_;
v___y_3941_ = v_recordedDeps_3997_;
v___y_3942_ = v_auxDeclNGen_3995_;
v___y_3943_ = v_nextMacroScope_3993_;
v___y_3944_ = v_traceState_3996_;
v___y_3945_ = v_infoState_3999_;
v___y_3946_ = v___y_3988_;
v___y_3947_ = v___x_4002_;
goto v___jp_3936_;
}
else
{
lean_object* v_env_4003_; lean_object* v_nextMacroScope_4004_; lean_object* v_ngen_4005_; lean_object* v_auxDeclNGen_4006_; lean_object* v_traceState_4007_; lean_object* v_recordedDeps_4008_; lean_object* v_messages_4009_; lean_object* v_infoState_4010_; lean_object* v_snapshotTasks_4011_; lean_object* v_asyncMode_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_env_4003_ = lean_ctor_get(v___x_3989_, 0);
lean_inc_ref(v_env_4003_);
v_nextMacroScope_4004_ = lean_ctor_get(v___x_3989_, 1);
lean_inc(v_nextMacroScope_4004_);
v_ngen_4005_ = lean_ctor_get(v___x_3989_, 2);
lean_inc_ref(v_ngen_4005_);
v_auxDeclNGen_4006_ = lean_ctor_get(v___x_3989_, 3);
lean_inc_ref(v_auxDeclNGen_4006_);
v_traceState_4007_ = lean_ctor_get(v___x_3989_, 4);
lean_inc_ref(v_traceState_4007_);
v_recordedDeps_4008_ = lean_ctor_get(v___x_3989_, 6);
lean_inc_ref(v_recordedDeps_4008_);
v_messages_4009_ = lean_ctor_get(v___x_3989_, 7);
lean_inc_ref(v_messages_4009_);
v_infoState_4010_ = lean_ctor_get(v___x_3989_, 8);
lean_inc_ref(v_infoState_4010_);
v_snapshotTasks_4011_ = lean_ctor_get(v___x_3989_, 9);
lean_inc_ref(v_snapshotTasks_4011_);
lean_dec(v___x_3989_);
v_asyncMode_4012_ = lean_ctor_get(v_toEnvExtension_3990_, 2);
lean_inc_ref_n(v_toEnvExtension_3990_, 2);
v___x_4013_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3990_, v_env_4003_);
lean_dec_ref(v_env_4003_);
v___x_4014_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3990_, v___x_4013_, v___f_3984_, v_asyncMode_4012_, v___x_3977_, v___x_3985_);
v___y_3937_ = v_ngen_4005_;
v___y_3938_ = v___y_3987_;
v___y_3939_ = v_snapshotTasks_4011_;
v___y_3940_ = v_messages_4009_;
v___y_3941_ = v_recordedDeps_4008_;
v___y_3942_ = v_auxDeclNGen_4006_;
v___y_3943_ = v_nextMacroScope_4004_;
v___y_3944_ = v_traceState_4007_;
v___y_3945_ = v_infoState_4010_;
v___y_3946_ = v___y_3988_;
v___y_3947_ = v___x_4014_;
goto v___jp_3936_;
}
}
}
else
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
lean_dec_ref_known(v_entry_3972_, 1);
lean_dec(v_hint_3930_);
lean_dec(v_mod_3928_);
v___x_4048_ = lean_box(0);
v___x_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
v___jp_3936_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v_mctx_3952_; lean_object* v_zetaDeltaFVarIds_3953_; lean_object* v_postponed_3954_; lean_object* v_diag_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3966_; 
v___x_3948_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
v___x_3949_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3949_, 0, v___y_3947_);
lean_ctor_set(v___x_3949_, 1, v___y_3943_);
lean_ctor_set(v___x_3949_, 2, v___y_3937_);
lean_ctor_set(v___x_3949_, 3, v___y_3942_);
lean_ctor_set(v___x_3949_, 4, v___y_3944_);
lean_ctor_set(v___x_3949_, 5, v___x_3948_);
lean_ctor_set(v___x_3949_, 6, v___y_3941_);
lean_ctor_set(v___x_3949_, 7, v___y_3940_);
lean_ctor_set(v___x_3949_, 8, v___y_3945_);
lean_ctor_set(v___x_3949_, 9, v___y_3939_);
v___x_3950_ = lean_st_ref_put(v___y_3946_, v___x_3949_);
v___x_3951_ = lean_st_ref_take(v___y_3938_);
v_mctx_3952_ = lean_ctor_get(v___x_3951_, 0);
v_zetaDeltaFVarIds_3953_ = lean_ctor_get(v___x_3951_, 2);
v_postponed_3954_ = lean_ctor_get(v___x_3951_, 3);
v_diag_3955_ = lean_ctor_get(v___x_3951_, 4);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3966_ == 0)
{
lean_object* v_unused_3967_; 
v_unused_3967_ = lean_ctor_get(v___x_3951_, 1);
lean_dec(v_unused_3967_);
v___x_3957_ = v___x_3951_;
v_isShared_3958_ = v_isSharedCheck_3966_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_diag_3955_);
lean_inc(v_postponed_3954_);
lean_inc(v_zetaDeltaFVarIds_3953_);
lean_inc(v_mctx_3952_);
lean_dec(v___x_3951_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3966_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3959_ = lean_box(0);
v___x_3960_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2);
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 1, v___x_3960_);
v___x_3962_ = v___x_3957_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_mctx_3952_);
lean_ctor_set(v_reuseFailAlloc_3965_, 1, v___x_3960_);
lean_ctor_set(v_reuseFailAlloc_3965_, 2, v_zetaDeltaFVarIds_3953_);
lean_ctor_set(v_reuseFailAlloc_3965_, 3, v_postponed_3954_);
lean_ctor_set(v_reuseFailAlloc_3965_, 4, v_diag_3955_);
v___x_3962_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_st_ref_put(v___y_3938_, v___x_3962_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3959_);
return v___x_3964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___boxed(lean_object* v_mod_4050_, lean_object* v_isMeta_4051_, lean_object* v_hint_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
uint8_t v_isMeta_boxed_4058_; lean_object* v_res_4059_; 
v_isMeta_boxed_4058_ = lean_unbox(v_isMeta_4051_);
v_res_4059_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_mod_4050_, v_isMeta_boxed_4058_, v_hint_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(lean_object* v_a_4060_, lean_object* v_x_4061_){
_start:
{
if (lean_obj_tag(v_x_4061_) == 0)
{
lean_object* v___x_4062_; 
v___x_4062_ = lean_box(0);
return v___x_4062_;
}
else
{
lean_object* v_key_4063_; lean_object* v_value_4064_; lean_object* v_tail_4065_; uint8_t v___x_4066_; 
v_key_4063_ = lean_ctor_get(v_x_4061_, 0);
v_value_4064_ = lean_ctor_get(v_x_4061_, 1);
v_tail_4065_ = lean_ctor_get(v_x_4061_, 2);
v___x_4066_ = lean_name_eq(v_key_4063_, v_a_4060_);
if (v___x_4066_ == 0)
{
v_x_4061_ = v_tail_4065_;
goto _start;
}
else
{
lean_object* v___x_4068_; 
lean_inc(v_value_4064_);
v___x_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4068_, 0, v_value_4064_);
return v___x_4068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_4069_, lean_object* v_x_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4069_, v_x_4070_);
lean_dec(v_x_4070_);
lean_dec(v_a_4069_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(lean_object* v_m_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_buckets_4074_; lean_object* v___x_4075_; uint64_t v___y_4077_; 
v_buckets_4074_ = lean_ctor_get(v_m_4072_, 1);
v___x_4075_ = lean_array_get_size(v_buckets_4074_);
if (lean_obj_tag(v_a_4073_) == 0)
{
uint64_t v___x_4091_; 
v___x_4091_ = 1723ULL;
v___y_4077_ = v___x_4091_;
goto v___jp_4076_;
}
else
{
uint64_t v_hash_4092_; 
v_hash_4092_ = lean_ctor_get_uint64(v_a_4073_, sizeof(void*)*2);
v___y_4077_ = v_hash_4092_;
goto v___jp_4076_;
}
v___jp_4076_:
{
uint64_t v___x_4078_; uint64_t v___x_4079_; uint64_t v_fold_4080_; uint64_t v___x_4081_; uint64_t v___x_4082_; uint64_t v___x_4083_; size_t v___x_4084_; size_t v___x_4085_; size_t v___x_4086_; size_t v___x_4087_; size_t v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4078_ = 32ULL;
v___x_4079_ = lean_uint64_shift_right(v___y_4077_, v___x_4078_);
v_fold_4080_ = lean_uint64_xor(v___y_4077_, v___x_4079_);
v___x_4081_ = 16ULL;
v___x_4082_ = lean_uint64_shift_right(v_fold_4080_, v___x_4081_);
v___x_4083_ = lean_uint64_xor(v_fold_4080_, v___x_4082_);
v___x_4084_ = lean_uint64_to_usize(v___x_4083_);
v___x_4085_ = lean_usize_of_nat(v___x_4075_);
v___x_4086_ = ((size_t)1ULL);
v___x_4087_ = lean_usize_sub(v___x_4085_, v___x_4086_);
v___x_4088_ = lean_usize_land(v___x_4084_, v___x_4087_);
v___x_4089_ = lean_array_uget_borrowed(v_buckets_4074_, v___x_4088_);
v___x_4090_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4073_, v___x_4089_);
return v___x_4090_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg___boxed(lean_object* v_m_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v_m_4093_, v_a_4094_);
lean_dec(v_a_4094_);
lean_dec_ref(v_m_4093_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v___x_4096_, lean_object* v_declName_4097_, lean_object* v_as_4098_, size_t v_sz_4099_, size_t v_i_4100_, lean_object* v_b_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
uint8_t v___x_4107_; 
v___x_4107_ = lean_usize_dec_lt(v_i_4100_, v_sz_4099_);
if (v___x_4107_ == 0)
{
lean_object* v___x_4108_; 
lean_dec(v_declName_4097_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_b_4101_);
return v___x_4108_;
}
else
{
lean_object* v___x_4109_; lean_object* v_modules_4110_; lean_object* v___x_4111_; lean_object* v_a_4112_; lean_object* v___x_4113_; lean_object* v_toImport_4114_; lean_object* v_module_4115_; lean_object* v___x_4116_; uint8_t v___x_4117_; lean_object* v___x_4118_; 
v___x_4109_ = l_Lean_Environment_header(v___x_4096_);
v_modules_4110_ = lean_ctor_get(v___x_4109_, 3);
lean_inc_ref(v_modules_4110_);
lean_dec_ref(v___x_4109_);
v___x_4111_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4112_ = lean_array_uget_borrowed(v_as_4098_, v_i_4100_);
v___x_4113_ = lean_array_get(v___x_4111_, v_modules_4110_, v_a_4112_);
lean_dec_ref(v_modules_4110_);
v_toImport_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc_ref(v_toImport_4114_);
lean_dec(v___x_4113_);
v_module_4115_ = lean_ctor_get(v_toImport_4114_, 0);
lean_inc(v_module_4115_);
lean_dec_ref(v_toImport_4114_);
v___x_4116_ = lean_box(0);
v___x_4117_ = 0;
lean_inc(v_declName_4097_);
v___x_4118_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_module_4115_, v___x_4117_, v_declName_4097_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
if (lean_obj_tag(v___x_4118_) == 0)
{
size_t v___x_4119_; size_t v___x_4120_; 
lean_dec_ref_known(v___x_4118_, 1);
v___x_4119_ = ((size_t)1ULL);
v___x_4120_ = lean_usize_add(v_i_4100_, v___x_4119_);
v_i_4100_ = v___x_4120_;
v_b_4101_ = v___x_4116_;
goto _start;
}
else
{
lean_dec(v_declName_4097_);
return v___x_4118_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v___x_4122_, lean_object* v_declName_4123_, lean_object* v_as_4124_, lean_object* v_sz_4125_, lean_object* v_i_4126_, lean_object* v_b_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
size_t v_sz_boxed_4133_; size_t v_i_boxed_4134_; lean_object* v_res_4135_; 
v_sz_boxed_4133_ = lean_unbox_usize(v_sz_4125_);
lean_dec(v_sz_4125_);
v_i_boxed_4134_ = lean_unbox_usize(v_i_4126_);
lean_dec(v_i_4126_);
v_res_4135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v___x_4122_, v_declName_4123_, v_as_4124_, v_sz_boxed_4133_, v_i_boxed_4134_, v_b_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec_ref(v_as_4124_);
lean_dec_ref(v___x_4122_);
return v_res_4135_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Std_HashMap_instInhabited___redArg();
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_4139_, uint8_t v_isMeta_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v_env_4151_; lean_object* v___y_4153_; lean_object* v___x_4166_; 
v___x_4146_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_4147_ = lean_st_ref_get(v___y_4144_);
v_env_4151_ = lean_ctor_get(v___x_4147_, 0);
lean_inc_ref(v_env_4151_);
lean_dec(v___x_4147_);
v___x_4166_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4151_, v_declName_4139_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_dec_ref(v_env_4151_);
lean_dec(v_declName_4139_);
goto v___jp_4148_;
}
else
{
lean_object* v_val_4167_; lean_object* v___x_4168_; lean_object* v_modules_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; 
v_val_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_val_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v___x_4168_ = l_Lean_Environment_header(v_env_4151_);
v_modules_4169_ = lean_ctor_get(v___x_4168_, 3);
lean_inc_ref(v_modules_4169_);
lean_dec_ref(v___x_4168_);
v___x_4170_ = lean_array_get_size(v_modules_4169_);
v___x_4171_ = lean_nat_dec_lt(v_val_4167_, v___x_4170_);
if (v___x_4171_ == 0)
{
lean_dec_ref(v_modules_4169_);
lean_dec(v_val_4167_);
lean_dec_ref(v_env_4151_);
lean_dec(v_declName_4139_);
goto v___jp_4148_;
}
else
{
lean_object* v___x_4172_; lean_object* v___x_4173_; uint8_t v___y_4175_; 
v___x_4172_ = lean_array_fget(v_modules_4169_, v_val_4167_);
lean_dec(v_val_4167_);
lean_dec_ref(v_modules_4169_);
v___x_4173_ = lean_st_ref_get(v___y_4144_);
if (v_isMeta_4140_ == 0)
{
lean_dec(v___x_4173_);
v___y_4175_ = v_isMeta_4140_;
goto v___jp_4174_;
}
else
{
lean_object* v_env_4186_; uint8_t v___x_4187_; 
v_env_4186_ = lean_ctor_get(v___x_4173_, 0);
lean_inc_ref(v_env_4186_);
lean_dec(v___x_4173_);
lean_inc(v_declName_4139_);
v___x_4187_ = l_Lean_isMarkedMeta(v_env_4186_, v_declName_4139_);
if (v___x_4187_ == 0)
{
v___y_4175_ = v_isMeta_4140_;
goto v___jp_4174_;
}
else
{
uint8_t v___x_4188_; 
v___x_4188_ = 0;
v___y_4175_ = v___x_4188_;
goto v___jp_4174_;
}
}
v___jp_4174_:
{
lean_object* v_toImport_4176_; lean_object* v_module_4177_; lean_object* v___x_4178_; 
v_toImport_4176_ = lean_ctor_get(v___x_4172_, 0);
lean_inc_ref(v_toImport_4176_);
lean_dec(v___x_4172_);
v_module_4177_ = lean_ctor_get(v_toImport_4176_, 0);
lean_inc(v_module_4177_);
lean_dec_ref(v_toImport_4176_);
lean_inc(v_declName_4139_);
v___x_4178_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_module_4177_, v___y_4175_, v_declName_4139_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
lean_dec_ref_known(v___x_4178_, 1);
v___x_4179_ = l_Lean_indirectModUseExt;
v___x_4180_ = lean_box(1);
v___x_4181_ = lean_box(0);
lean_inc_ref(v_env_4151_);
v___x_4182_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4146_, v___x_4179_, v_env_4151_, v___x_4180_, v___x_4181_);
v___x_4183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4182_, v_declName_4139_);
lean_dec(v___x_4182_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v___x_4184_; 
v___x_4184_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_4153_ = v___x_4184_;
goto v___jp_4152_;
}
else
{
lean_object* v_val_4185_; 
v_val_4185_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_val_4185_);
lean_dec_ref_known(v___x_4183_, 1);
v___y_4153_ = v_val_4185_;
goto v___jp_4152_;
}
}
else
{
lean_dec_ref(v_env_4151_);
lean_dec(v_declName_4139_);
return v___x_4178_;
}
}
}
}
v___jp_4148_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_box(0);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
return v___x_4150_;
}
v___jp_4152_:
{
lean_object* v___x_4154_; size_t v_sz_4155_; size_t v___x_4156_; lean_object* v___x_4157_; 
v___x_4154_ = lean_box(0);
v_sz_4155_ = lean_array_size(v___y_4153_);
v___x_4156_ = ((size_t)0ULL);
v___x_4157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_env_4151_, v_declName_4139_, v___y_4153_, v_sz_4155_, v___x_4156_, v___x_4154_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec_ref(v___y_4153_);
lean_dec_ref(v_env_4151_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4164_ == 0)
{
lean_object* v_unused_4165_; 
v_unused_4165_ = lean_ctor_get(v___x_4157_, 0);
lean_dec(v_unused_4165_);
v___x_4159_ = v___x_4157_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_dec(v___x_4157_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 0, v___x_4154_);
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4154_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
else
{
return v___x_4157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_4189_, lean_object* v_isMeta_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
uint8_t v_isMeta_boxed_4196_; lean_object* v_res_4197_; 
v_isMeta_boxed_4196_ = lean_unbox(v_isMeta_4190_);
v_res_4197_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_4189_, v_isMeta_boxed_4196_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_4198_, uint8_t v_when_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
if (v_when_4199_ == 0)
{
lean_object* v___x_4205_; 
lean_inc(v___y_4203_);
lean_inc_ref(v___y_4202_);
lean_inc(v___y_4201_);
lean_inc_ref(v___y_4200_);
v___x_4205_ = lean_apply_5(v_x_4198_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, lean_box(0));
return v___x_4205_;
}
else
{
uint8_t v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = 0;
v___x_4207_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_4198_, v___x_4206_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
return v___x_4207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_4208_, lean_object* v_when_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
uint8_t v_when_boxed_4215_; lean_object* v_res_4216_; 
v_when_boxed_4215_ = lean_unbox(v_when_4209_);
v_res_4216_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_4208_, v_when_boxed_4215_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v_ext_4217_, uint8_t v_showInfo_4218_, uint8_t v_minIndexable_4219_, lean_object* v_attrName_4220_, lean_object* v___x_4221_, lean_object* v_declName_4222_, lean_object* v_stx_4223_, uint8_t v_attrKind_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
uint8_t v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___f_4233_; uint8_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4228_ = 0;
v___x_4229_ = lean_box(v_attrKind_4224_);
v___x_4230_ = lean_box(v_showInfo_4218_);
v___x_4231_ = lean_box(v_minIndexable_4219_);
v___x_4232_ = lean_box(v___x_4228_);
lean_inc(v_declName_4222_);
v___f_4233_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_4233_, 0, v_declName_4222_);
lean_closure_set(v___f_4233_, 1, v___x_4229_);
lean_closure_set(v___f_4233_, 2, v_stx_4223_);
lean_closure_set(v___f_4233_, 3, v_ext_4217_);
lean_closure_set(v___f_4233_, 4, v___x_4230_);
lean_closure_set(v___f_4233_, 5, v___x_4231_);
lean_closure_set(v___f_4233_, 6, v___x_4232_);
lean_closure_set(v___f_4233_, 7, v_attrName_4220_);
v___x_4234_ = 1;
v___x_4235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_4236_ = lean_unsigned_to_nat(32u);
v___x_4237_ = lean_mk_empty_array_with_capacity(v___x_4236_);
lean_dec_ref(v___x_4237_);
v___x_4238_ = lean_unsigned_to_nat(0u);
v___x_4239_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_4240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_4241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_4242_ = lean_box(0);
lean_inc(v___x_4221_);
v___x_4243_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4243_, 0, v___x_4235_);
lean_ctor_set(v___x_4243_, 1, v___x_4221_);
lean_ctor_set(v___x_4243_, 2, v___x_4240_);
lean_ctor_set(v___x_4243_, 3, v___x_4241_);
lean_ctor_set(v___x_4243_, 4, v___x_4242_);
lean_ctor_set(v___x_4243_, 5, v___x_4238_);
lean_ctor_set(v___x_4243_, 6, v___x_4242_);
lean_ctor_set_uint8(v___x_4243_, sizeof(void*)*7, v___x_4228_);
lean_ctor_set_uint8(v___x_4243_, sizeof(void*)*7 + 1, v___x_4228_);
lean_ctor_set_uint8(v___x_4243_, sizeof(void*)*7 + 2, v___x_4228_);
lean_ctor_set_uint8(v___x_4243_, sizeof(void*)*7 + 3, v___x_4234_);
v___x_4244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_4245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_4246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_4247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4244_);
lean_ctor_set(v___x_4247_, 1, v___x_4245_);
lean_ctor_set(v___x_4247_, 2, v___x_4221_);
lean_ctor_set(v___x_4247_, 3, v___x_4239_);
lean_ctor_set(v___x_4247_, 4, v___x_4246_);
v___x_4248_ = lean_st_mk_ref(v___x_4247_);
v___x_4249_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_4222_, v___x_4228_, v___x_4243_, v___x_4248_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v___x_4250_; 
lean_dec_ref_known(v___x_4249_, 1);
v___x_4250_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_4233_, v___x_4234_, v___x_4243_, v___x_4248_, v___y_4225_, v___y_4226_);
lean_dec_ref_known(v___x_4243_, 7);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4259_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4253_ = v___x_4250_;
v_isShared_4254_ = v_isSharedCheck_4259_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4250_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4259_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4255_; lean_object* v___x_4257_; 
v___x_4255_ = lean_st_ref_get(v___x_4248_);
lean_dec(v___x_4248_);
lean_dec(v___x_4255_);
if (v_isShared_4254_ == 0)
{
v___x_4257_ = v___x_4253_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4251_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
else
{
lean_dec(v___x_4248_);
return v___x_4250_;
}
}
else
{
lean_dec(v___x_4248_);
lean_dec_ref_known(v___x_4243_, 7);
lean_dec_ref(v___f_4233_);
return v___x_4249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v_ext_4260_, lean_object* v_showInfo_4261_, lean_object* v_minIndexable_4262_, lean_object* v_attrName_4263_, lean_object* v___x_4264_, lean_object* v_declName_4265_, lean_object* v_stx_4266_, lean_object* v_attrKind_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
uint8_t v_showInfo_boxed_4271_; uint8_t v_minIndexable_boxed_4272_; uint8_t v_attrKind_boxed_4273_; lean_object* v_res_4274_; 
v_showInfo_boxed_4271_ = lean_unbox(v_showInfo_4261_);
v_minIndexable_boxed_4272_ = lean_unbox(v_minIndexable_4262_);
v_attrKind_boxed_4273_ = lean_unbox(v_attrKind_4267_);
v_res_4274_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v_ext_4260_, v_showInfo_boxed_4271_, v_minIndexable_boxed_4272_, v_attrName_4263_, v___x_4264_, v_declName_4265_, v_stx_4266_, v_attrKind_boxed_4273_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_4297_, uint8_t v_minIndexable_4298_, uint8_t v_showInfo_4299_, lean_object* v_ext_4300_, lean_object* v_ref_4301_){
_start:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___f_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___f_4308_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4354_; 
v___x_4303_ = lean_box(1);
v___x_4304_ = lean_box(v_showInfo_4299_);
lean_inc_n(v_attrName_4297_, 2);
lean_inc_ref(v_ext_4300_);
v___f_4305_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_4305_, 0, v_ext_4300_);
lean_closure_set(v___f_4305_, 1, v___x_4303_);
lean_closure_set(v___f_4305_, 2, v___x_4304_);
lean_closure_set(v___f_4305_, 3, v_attrName_4297_);
v___x_4306_ = lean_box(v_showInfo_4299_);
v___x_4307_ = lean_box(v_minIndexable_4298_);
v___f_4308_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_4308_, 0, v_ext_4300_);
lean_closure_set(v___f_4308_, 1, v___x_4306_);
lean_closure_set(v___f_4308_, 2, v___x_4307_);
lean_closure_set(v___f_4308_, 3, v_attrName_4297_);
lean_closure_set(v___f_4308_, 4, v___x_4303_);
if (v_minIndexable_4298_ == 0)
{
if (v_showInfo_4299_ == 0)
{
lean_inc(v_attrName_4297_);
v___y_4354_ = v_attrName_4297_;
goto v___jp_4353_;
}
else
{
lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_4297_);
v___x_4383_ = lean_name_append_after(v_attrName_4297_, v___x_4382_);
v___y_4354_ = v___x_4383_;
goto v___jp_4353_;
}
}
else
{
if (v_showInfo_4299_ == 0)
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_4297_);
v___x_4385_ = lean_name_append_after(v_attrName_4297_, v___x_4384_);
v___y_4354_ = v___x_4385_;
goto v___jp_4353_;
}
else
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_4297_);
v___x_4387_ = lean_name_append_after(v_attrName_4297_, v___x_4386_);
v___y_4354_ = v___x_4387_;
goto v___jp_4353_;
}
}
v___jp_4309_:
{
lean_object* v___x_4312_; uint8_t v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; uint8_t v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_4313_ = 1;
v___x_4314_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4297_, v___x_4313_);
v___x_4315_ = lean_string_append(v___x_4312_, v___x_4314_);
v___x_4316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_4317_ = lean_string_append(v___x_4315_, v___x_4316_);
v___x_4318_ = lean_string_append(v___x_4317_, v___x_4314_);
v___x_4319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_4320_ = lean_string_append(v___x_4318_, v___x_4319_);
v___x_4321_ = lean_string_append(v___x_4320_, v___x_4314_);
v___x_4322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_4323_ = lean_string_append(v___x_4321_, v___x_4322_);
v___x_4324_ = lean_string_append(v___x_4323_, v___x_4314_);
v___x_4325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_4326_ = lean_string_append(v___x_4324_, v___x_4325_);
v___x_4327_ = lean_string_append(v___x_4326_, v___x_4314_);
v___x_4328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_4329_ = lean_string_append(v___x_4327_, v___x_4328_);
v___x_4330_ = lean_string_append(v___x_4329_, v___x_4314_);
v___x_4331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_4332_ = lean_string_append(v___x_4330_, v___x_4331_);
v___x_4333_ = lean_string_append(v___x_4332_, v___x_4314_);
v___x_4334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_4335_ = lean_string_append(v___x_4333_, v___x_4334_);
v___x_4336_ = lean_string_append(v___x_4335_, v___x_4314_);
v___x_4337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_4338_ = lean_string_append(v___x_4336_, v___x_4337_);
v___x_4339_ = lean_string_append(v___x_4338_, v___x_4314_);
v___x_4340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_4341_ = lean_string_append(v___x_4339_, v___x_4340_);
v___x_4342_ = lean_string_append(v___x_4341_, v___x_4314_);
v___x_4343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_4344_ = lean_string_append(v___x_4342_, v___x_4343_);
v___x_4345_ = lean_string_append(v___x_4344_, v___x_4314_);
lean_dec_ref(v___x_4314_);
v___x_4346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_4347_ = lean_string_append(v___x_4345_, v___x_4346_);
v___x_4348_ = lean_string_append(v___y_4311_, v___x_4347_);
lean_dec_ref(v___x_4347_);
v___x_4349_ = 1;
v___x_4350_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4350_, 0, v_ref_4301_);
lean_ctor_set(v___x_4350_, 1, v___y_4310_);
lean_ctor_set(v___x_4350_, 2, v___x_4348_);
lean_ctor_set_uint8(v___x_4350_, sizeof(void*)*3, v___x_4349_);
v___x_4351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4350_);
lean_ctor_set(v___x_4351_, 1, v___f_4308_);
lean_ctor_set(v___x_4351_, 2, v___f_4305_);
v___x_4352_ = l_Lean_registerBuiltinAttribute(v___x_4351_);
return v___x_4352_;
}
v___jp_4353_:
{
if (v_minIndexable_4298_ == 0)
{
if (v_showInfo_4299_ == 0)
{
lean_object* v___x_4355_; uint8_t v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_4356_ = 1;
lean_inc(v_attrName_4297_);
v___x_4357_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4297_, v___x_4356_);
v___x_4358_ = lean_string_append(v___x_4355_, v___x_4357_);
lean_dec_ref(v___x_4357_);
v___x_4359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_4360_ = lean_string_append(v___x_4358_, v___x_4359_);
v___y_4310_ = v___y_4354_;
v___y_4311_ = v___x_4360_;
goto v___jp_4309_;
}
else
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4297_);
v___x_4362_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4297_, v_showInfo_4299_);
v___x_4363_ = lean_string_append(v___x_4361_, v___x_4362_);
v___x_4364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_4365_ = lean_string_append(v___x_4363_, v___x_4364_);
v___x_4366_ = lean_string_append(v___x_4365_, v___x_4362_);
lean_dec_ref(v___x_4362_);
v___x_4367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_4368_ = lean_string_append(v___x_4366_, v___x_4367_);
v___y_4310_ = v___y_4354_;
v___y_4311_ = v___x_4368_;
goto v___jp_4309_;
}
}
else
{
if (v_showInfo_4299_ == 0)
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4297_);
v___x_4370_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4297_, v_minIndexable_4298_);
v___x_4371_ = lean_string_append(v___x_4369_, v___x_4370_);
lean_dec_ref(v___x_4370_);
v___x_4372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_4373_ = lean_string_append(v___x_4371_, v___x_4372_);
v___y_4310_ = v___y_4354_;
v___y_4311_ = v___x_4373_;
goto v___jp_4309_;
}
else
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4297_);
v___x_4375_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4297_, v_showInfo_4299_);
v___x_4376_ = lean_string_append(v___x_4374_, v___x_4375_);
v___x_4377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_4378_ = lean_string_append(v___x_4376_, v___x_4377_);
v___x_4379_ = lean_string_append(v___x_4378_, v___x_4375_);
lean_dec_ref(v___x_4375_);
v___x_4380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_4381_ = lean_string_append(v___x_4379_, v___x_4380_);
v___y_4310_ = v___y_4354_;
v___y_4311_ = v___x_4381_;
goto v___jp_4309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_4388_, lean_object* v_minIndexable_4389_, lean_object* v_showInfo_4390_, lean_object* v_ext_4391_, lean_object* v_ref_4392_, lean_object* v_a_4393_){
_start:
{
uint8_t v_minIndexable_boxed_4394_; uint8_t v_showInfo_boxed_4395_; lean_object* v_res_4396_; 
v_minIndexable_boxed_4394_ = lean_unbox(v_minIndexable_4389_);
v_showInfo_boxed_4395_ = lean_unbox(v_showInfo_4390_);
v_res_4396_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4388_, v_minIndexable_boxed_4394_, v_showInfo_boxed_4395_, v_ext_4391_, v_ref_4392_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_4397_, lean_object* v_msg_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v___x_4404_; 
v___x_4404_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_4405_, lean_object* v_msg_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_4405_, v_msg_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_4413_, uint8_t v_attrKind_4414_, uint8_t v_showInfo_4415_, uint8_t v_minIndexable_4416_, lean_object* v_as_4417_, lean_object* v_as_x27_4418_, lean_object* v_b_4419_, lean_object* v_a_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_4413_, v_attrKind_4414_, v_showInfo_4415_, v_minIndexable_4416_, v_as_x27_4418_, v_b_4419_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_4427_, lean_object* v_attrKind_4428_, lean_object* v_showInfo_4429_, lean_object* v_minIndexable_4430_, lean_object* v_as_4431_, lean_object* v_as_x27_4432_, lean_object* v_b_4433_, lean_object* v_a_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
uint8_t v_attrKind_boxed_4440_; uint8_t v_showInfo_boxed_4441_; uint8_t v_minIndexable_boxed_4442_; lean_object* v_res_4443_; 
v_attrKind_boxed_4440_ = lean_unbox(v_attrKind_4428_);
v_showInfo_boxed_4441_ = lean_unbox(v_showInfo_4429_);
v_minIndexable_boxed_4442_ = lean_unbox(v_minIndexable_4430_);
v_res_4443_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_4427_, v_attrKind_boxed_4440_, v_showInfo_boxed_4441_, v_minIndexable_boxed_4442_, v_as_4431_, v_as_x27_4432_, v_b_4433_, v_a_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v_as_x27_4432_);
lean_dec(v_as_4431_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_4444_, lean_object* v_x_4445_, uint8_t v_when_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_4445_, v_when_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_4453_, lean_object* v_x_4454_, lean_object* v_when_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
uint8_t v_when_boxed_4461_; lean_object* v_res_4462_; 
v_when_boxed_4461_ = lean_unbox(v_when_4455_);
v_res_4462_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_4453_, v_x_4454_, v_when_boxed_4461_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v_00_u03b2_4463_, lean_object* v_m_4464_, lean_object* v_a_4465_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v_m_4464_, v_a_4465_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4467_, lean_object* v_m_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_00_u03b2_4467_, v_m_4468_, v_a_4469_);
lean_dec(v_a_4469_);
lean_dec_ref(v_m_4468_);
return v_res_4470_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_4471_, lean_object* v_x_4472_, lean_object* v_x_4473_){
_start:
{
uint8_t v___x_4474_; 
v___x_4474_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v_x_4472_, v_x_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4475_, lean_object* v_x_4476_, lean_object* v_x_4477_){
_start:
{
uint8_t v_res_4478_; lean_object* v_r_4479_; 
v_res_4478_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(v_00_u03b2_4475_, v_x_4476_, v_x_4477_);
lean_dec_ref(v_x_4477_);
lean_dec_ref(v_x_4476_);
v_r_4479_ = lean_box(v_res_4478_);
return v_r_4479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4480_, lean_object* v_a_4481_, lean_object* v_x_4482_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4481_, v_x_4482_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4484_, lean_object* v_a_4485_, lean_object* v_x_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(v_00_u03b2_4484_, v_a_4485_, v_x_4486_);
lean_dec(v_x_4486_);
lean_dec(v_a_4485_);
return v_res_4487_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4488_, lean_object* v_x_4489_, size_t v_x_4490_, lean_object* v_x_4491_){
_start:
{
uint8_t v___x_4492_; 
v___x_4492_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_4489_, v_x_4490_, v_x_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4493_, lean_object* v_x_4494_, lean_object* v_x_4495_, lean_object* v_x_4496_){
_start:
{
size_t v_x_12868__boxed_4497_; uint8_t v_res_4498_; lean_object* v_r_4499_; 
v_x_12868__boxed_4497_ = lean_unbox_usize(v_x_4495_);
lean_dec(v_x_4495_);
v_res_4498_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(v_00_u03b2_4493_, v_x_4494_, v_x_12868__boxed_4497_, v_x_4496_);
lean_dec_ref(v_x_4496_);
lean_dec_ref(v_x_4494_);
v_r_4499_ = lean_box(v_res_4498_);
return v_r_4499_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4500_, lean_object* v_keys_4501_, lean_object* v_vals_4502_, lean_object* v_heq_4503_, lean_object* v_i_4504_, lean_object* v_k_4505_){
_start:
{
uint8_t v___x_4506_; 
v___x_4506_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_keys_4501_, v_i_4504_, v_k_4505_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_4507_, lean_object* v_keys_4508_, lean_object* v_vals_4509_, lean_object* v_heq_4510_, lean_object* v_i_4511_, lean_object* v_k_4512_){
_start:
{
uint8_t v_res_4513_; lean_object* v_r_4514_; 
v_res_4513_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(v_00_u03b2_4507_, v_keys_4508_, v_vals_4509_, v_heq_4510_, v_i_4511_, v_k_4512_);
lean_dec_ref(v_k_4512_);
lean_dec_ref(v_vals_4509_);
lean_dec_ref(v_keys_4508_);
v_r_4514_ = lean_box(v_res_4513_);
return v_r_4514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4515_ = lean_box(0);
v___x_4516_ = lean_unsigned_to_nat(16u);
v___x_4517_ = lean_mk_array(v___x_4516_, v___x_4515_);
return v___x_4517_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_4519_ = lean_unsigned_to_nat(0u);
v___x_4520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
lean_ctor_set(v___x_4520_, 1, v___x_4518_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_4523_ = lean_st_mk_ref(v___x_4522_);
v___x_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_4527_, lean_object* v_msg_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v_ref_4532_; lean_object* v___x_4533_; lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4579_; 
v_ref_4532_ = lean_ctor_get(v___y_4529_, 2);
v___x_4533_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_4528_, v___y_4529_, v___y_4530_);
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4579_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4579_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4538_; lean_object* v_traceState_4539_; lean_object* v_env_4540_; lean_object* v_nextMacroScope_4541_; lean_object* v_ngen_4542_; lean_object* v_auxDeclNGen_4543_; lean_object* v_cache_4544_; lean_object* v_recordedDeps_4545_; lean_object* v_messages_4546_; lean_object* v_infoState_4547_; lean_object* v_snapshotTasks_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4578_; 
v___x_4538_ = lean_st_ref_take(v___y_4530_);
v_traceState_4539_ = lean_ctor_get(v___x_4538_, 4);
v_env_4540_ = lean_ctor_get(v___x_4538_, 0);
v_nextMacroScope_4541_ = lean_ctor_get(v___x_4538_, 1);
v_ngen_4542_ = lean_ctor_get(v___x_4538_, 2);
v_auxDeclNGen_4543_ = lean_ctor_get(v___x_4538_, 3);
v_cache_4544_ = lean_ctor_get(v___x_4538_, 5);
v_recordedDeps_4545_ = lean_ctor_get(v___x_4538_, 6);
v_messages_4546_ = lean_ctor_get(v___x_4538_, 7);
v_infoState_4547_ = lean_ctor_get(v___x_4538_, 8);
v_snapshotTasks_4548_ = lean_ctor_get(v___x_4538_, 9);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4550_ = v___x_4538_;
v_isShared_4551_ = v_isSharedCheck_4578_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_snapshotTasks_4548_);
lean_inc(v_infoState_4547_);
lean_inc(v_messages_4546_);
lean_inc(v_recordedDeps_4545_);
lean_inc(v_cache_4544_);
lean_inc(v_traceState_4539_);
lean_inc(v_auxDeclNGen_4543_);
lean_inc(v_ngen_4542_);
lean_inc(v_nextMacroScope_4541_);
lean_inc(v_env_4540_);
lean_dec(v___x_4538_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4578_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
uint64_t v_tid_4552_; lean_object* v_traces_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4577_; 
v_tid_4552_ = lean_ctor_get_uint64(v_traceState_4539_, sizeof(void*)*1);
v_traces_4553_ = lean_ctor_get(v_traceState_4539_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_traceState_4539_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4555_ = v_traceState_4539_;
v_isShared_4556_ = v_isSharedCheck_4577_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_traces_4553_);
lean_dec(v_traceState_4539_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4577_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; double v___x_4559_; uint8_t v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4568_; 
v___x_4557_ = lean_box(0);
v___x_4558_ = lean_box(0);
v___x_4559_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0);
v___x_4560_ = 0;
v___x_4561_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_4562_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4562_, 0, v_cls_4527_);
lean_ctor_set(v___x_4562_, 1, v___x_4558_);
lean_ctor_set(v___x_4562_, 2, v___x_4561_);
lean_ctor_set_float(v___x_4562_, sizeof(void*)*3, v___x_4559_);
lean_ctor_set_float(v___x_4562_, sizeof(void*)*3 + 8, v___x_4559_);
lean_ctor_set_uint8(v___x_4562_, sizeof(void*)*3 + 16, v___x_4560_);
v___x_4563_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2));
v___x_4564_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4562_);
lean_ctor_set(v___x_4564_, 1, v_a_4534_);
lean_ctor_set(v___x_4564_, 2, v___x_4563_);
lean_inc(v_ref_4532_);
v___x_4565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4565_, 0, v_ref_4532_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
v___x_4566_ = l_Lean_PersistentArray_push___redArg(v_traces_4553_, v___x_4565_);
if (v_isShared_4556_ == 0)
{
lean_ctor_set(v___x_4555_, 0, v___x_4566_);
v___x_4568_ = v___x_4555_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4566_);
lean_ctor_set_uint64(v_reuseFailAlloc_4576_, sizeof(void*)*1, v_tid_4552_);
v___x_4568_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
lean_object* v___x_4570_; 
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 4, v___x_4568_);
v___x_4570_ = v___x_4550_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_env_4540_);
lean_ctor_set(v_reuseFailAlloc_4575_, 1, v_nextMacroScope_4541_);
lean_ctor_set(v_reuseFailAlloc_4575_, 2, v_ngen_4542_);
lean_ctor_set(v_reuseFailAlloc_4575_, 3, v_auxDeclNGen_4543_);
lean_ctor_set(v_reuseFailAlloc_4575_, 4, v___x_4568_);
lean_ctor_set(v_reuseFailAlloc_4575_, 5, v_cache_4544_);
lean_ctor_set(v_reuseFailAlloc_4575_, 6, v_recordedDeps_4545_);
lean_ctor_set(v_reuseFailAlloc_4575_, 7, v_messages_4546_);
lean_ctor_set(v_reuseFailAlloc_4575_, 8, v_infoState_4547_);
lean_ctor_set(v_reuseFailAlloc_4575_, 9, v_snapshotTasks_4548_);
v___x_4570_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
lean_object* v___x_4571_; lean_object* v___x_4573_; 
v___x_4571_ = lean_st_ref_put(v___y_4530_, v___x_4570_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v___x_4557_);
v___x_4573_ = v___x_4536_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4557_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_4580_, lean_object* v_msg_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_4580_, v_msg_4581_, v___y_4582_, v___y_4583_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_4586_, uint8_t v_isMeta_4587_, lean_object* v_hint_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v___y_4602_; lean_object* v___y_4603_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v_env_4610_; uint8_t v_isExporting_4611_; lean_object* v_entry_4612_; lean_object* v___x_4613_; lean_object* v_env_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; 
v___x_4608_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0);
v___x_4609_ = lean_st_ref_get(v___y_4590_);
v_env_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc_ref(v_env_4610_);
lean_dec(v___x_4609_);
v_isExporting_4611_ = lean_ctor_get_uint8(v_env_4610_, sizeof(void*)*13);
lean_dec_ref(v_env_4610_);
lean_inc(v_mod_4586_);
v_entry_4612_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_4612_, 0, v_mod_4586_);
lean_ctor_set_uint8(v_entry_4612_, sizeof(void*)*1, v_isExporting_4611_);
lean_ctor_set_uint8(v_entry_4612_, sizeof(void*)*1 + 1, v_isMeta_4587_);
v___x_4613_ = lean_st_ref_get(v___y_4590_);
v_env_4614_ = lean_ctor_get(v___x_4613_, 0);
lean_inc_ref(v_env_4614_);
lean_dec(v___x_4613_);
v___x_4615_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_4616_ = lean_box(1);
v___x_4617_ = lean_box(0);
v___x_4618_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4608_, v___x_4615_, v_env_4614_, v___x_4616_, v___x_4617_);
v___x_4619_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v___x_4618_, v_entry_4612_);
lean_dec(v___x_4618_);
if (v___x_4619_ == 0)
{
lean_object* v_toCold_4620_; lean_object* v_options_4621_; lean_object* v_inheritedTraceOptions_4622_; uint8_t v_hasTrace_4623_; lean_object* v___f_4624_; uint8_t v___x_4625_; lean_object* v___y_4627_; 
v_toCold_4620_ = lean_ctor_get(v___y_4589_, 0);
v_options_4621_ = lean_ctor_get(v_toCold_4620_, 2);
v_inheritedTraceOptions_4622_ = lean_ctor_get(v_toCold_4620_, 11);
v_hasTrace_4623_ = lean_ctor_get_uint8(v_options_4621_, sizeof(void*)*1);
v___f_4624_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_4624_, 0, v___x_4615_);
lean_closure_set(v___f_4624_, 1, v_entry_4612_);
v___x_4625_ = 1;
if (v_hasTrace_4623_ == 0)
{
lean_dec(v_hint_4588_);
lean_dec(v_mod_4586_);
v___y_4627_ = v___y_4590_;
goto v___jp_4626_;
}
else
{
lean_object* v_cls_4645_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___x_4665_; uint8_t v___x_4666_; 
v_cls_4645_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_4665_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8);
v___x_4666_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4622_, v_options_4621_, v___x_4665_);
if (v___x_4666_ == 0)
{
lean_dec(v_hint_4588_);
lean_dec(v_mod_4586_);
v___y_4627_ = v___y_4590_;
goto v___jp_4626_;
}
else
{
lean_object* v___x_4667_; lean_object* v___y_4669_; 
v___x_4667_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10);
if (v_isExporting_4611_ == 0)
{
lean_object* v___x_4676_; 
v___x_4676_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15));
v___y_4669_ = v___x_4676_;
goto v___jp_4668_;
}
else
{
lean_object* v___x_4677_; 
v___x_4677_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16));
v___y_4669_ = v___x_4677_;
goto v___jp_4668_;
}
v___jp_4668_:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
lean_inc_ref(v___y_4669_);
v___x_4670_ = l_Lean_stringToMessageData(v___y_4669_);
v___x_4671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4667_);
lean_ctor_set(v___x_4671_, 1, v___x_4670_);
v___x_4672_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12);
v___x_4673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4671_);
lean_ctor_set(v___x_4673_, 1, v___x_4672_);
if (v_isMeta_4587_ == 0)
{
lean_object* v___x_4674_; 
v___x_4674_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13));
v___y_4652_ = v___x_4673_;
v___y_4653_ = v___x_4674_;
goto v___jp_4651_;
}
else
{
lean_object* v___x_4675_; 
v___x_4675_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14));
v___y_4652_ = v___x_4673_;
v___y_4653_ = v___x_4675_;
goto v___jp_4651_;
}
}
}
v___jp_4646_:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4649_, 0, v___y_4647_);
lean_ctor_set(v___x_4649_, 1, v___y_4648_);
v___x_4650_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_4645_, v___x_4649_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_dec_ref_known(v___x_4650_, 1);
v___y_4627_ = v___y_4590_;
goto v___jp_4626_;
}
else
{
lean_dec_ref(v___f_4624_);
return v___x_4650_;
}
}
v___jp_4651_:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; uint8_t v___x_4660_; 
lean_inc_ref(v___y_4653_);
v___x_4654_ = l_Lean_stringToMessageData(v___y_4653_);
v___x_4655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4655_, 0, v___y_4652_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
v___x_4656_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4);
v___x_4657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4655_);
lean_ctor_set(v___x_4657_, 1, v___x_4656_);
v___x_4658_ = l_Lean_MessageData_ofName(v_mod_4586_);
v___x_4659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4657_);
lean_ctor_set(v___x_4659_, 1, v___x_4658_);
v___x_4660_ = l_Lean_Name_isAnonymous(v_hint_4588_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6);
v___x_4662_ = l_Lean_MessageData_ofName(v_hint_4588_);
v___x_4663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4661_);
lean_ctor_set(v___x_4663_, 1, v___x_4662_);
v___y_4647_ = v___x_4659_;
v___y_4648_ = v___x_4663_;
goto v___jp_4646_;
}
else
{
lean_object* v___x_4664_; 
lean_dec(v_hint_4588_);
v___x_4664_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7);
v___y_4647_ = v___x_4659_;
v___y_4648_ = v___x_4664_;
goto v___jp_4646_;
}
}
}
v___jp_4626_:
{
lean_object* v___x_4628_; lean_object* v_toEnvExtension_4629_; lean_object* v_env_4630_; lean_object* v_nextMacroScope_4631_; lean_object* v_ngen_4632_; lean_object* v_auxDeclNGen_4633_; lean_object* v_traceState_4634_; lean_object* v_recordedDeps_4635_; lean_object* v_messages_4636_; lean_object* v_infoState_4637_; lean_object* v_snapshotTasks_4638_; lean_object* v_asyncMode_4639_; uint8_t v_logWrites_4640_; lean_object* v___x_4641_; 
v___x_4628_ = lean_st_ref_take(v___y_4627_);
v_toEnvExtension_4629_ = lean_ctor_get(v___x_4615_, 0);
v_env_4630_ = lean_ctor_get(v___x_4628_, 0);
lean_inc_ref(v_env_4630_);
v_nextMacroScope_4631_ = lean_ctor_get(v___x_4628_, 1);
lean_inc(v_nextMacroScope_4631_);
v_ngen_4632_ = lean_ctor_get(v___x_4628_, 2);
lean_inc_ref(v_ngen_4632_);
v_auxDeclNGen_4633_ = lean_ctor_get(v___x_4628_, 3);
lean_inc_ref(v_auxDeclNGen_4633_);
v_traceState_4634_ = lean_ctor_get(v___x_4628_, 4);
lean_inc_ref(v_traceState_4634_);
v_recordedDeps_4635_ = lean_ctor_get(v___x_4628_, 6);
lean_inc_ref(v_recordedDeps_4635_);
v_messages_4636_ = lean_ctor_get(v___x_4628_, 7);
lean_inc_ref(v_messages_4636_);
v_infoState_4637_ = lean_ctor_get(v___x_4628_, 8);
lean_inc_ref(v_infoState_4637_);
v_snapshotTasks_4638_ = lean_ctor_get(v___x_4628_, 9);
lean_inc_ref(v_snapshotTasks_4638_);
lean_dec(v___x_4628_);
v_asyncMode_4639_ = lean_ctor_get(v_toEnvExtension_4629_, 2);
v_logWrites_4640_ = lean_ctor_get_uint8(v_toEnvExtension_4629_, sizeof(void*)*6);
v___x_4641_ = lean_box(0);
if (v_logWrites_4640_ == 0)
{
lean_object* v___x_4642_; 
lean_inc_ref(v_toEnvExtension_4629_);
v___x_4642_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4629_, v_env_4630_, v___f_4624_, v_asyncMode_4639_, v___x_4617_, v___x_4625_);
v___y_4593_ = v_recordedDeps_4635_;
v___y_4594_ = v_ngen_4632_;
v___y_4595_ = v_nextMacroScope_4631_;
v___y_4596_ = v___x_4641_;
v___y_4597_ = v_snapshotTasks_4638_;
v___y_4598_ = v___y_4627_;
v___y_4599_ = v_infoState_4637_;
v___y_4600_ = v_traceState_4634_;
v___y_4601_ = v_auxDeclNGen_4633_;
v___y_4602_ = v_messages_4636_;
v___y_4603_ = v___x_4642_;
goto v___jp_4592_;
}
else
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
lean_inc_ref_n(v_toEnvExtension_4629_, 2);
v___x_4643_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4629_, v_env_4630_);
lean_dec_ref(v_env_4630_);
v___x_4644_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4629_, v___x_4643_, v___f_4624_, v_asyncMode_4639_, v___x_4617_, v___x_4625_);
v___y_4593_ = v_recordedDeps_4635_;
v___y_4594_ = v_ngen_4632_;
v___y_4595_ = v_nextMacroScope_4631_;
v___y_4596_ = v___x_4641_;
v___y_4597_ = v_snapshotTasks_4638_;
v___y_4598_ = v___y_4627_;
v___y_4599_ = v_infoState_4637_;
v___y_4600_ = v_traceState_4634_;
v___y_4601_ = v_auxDeclNGen_4633_;
v___y_4602_ = v_messages_4636_;
v___y_4603_ = v___x_4644_;
goto v___jp_4592_;
}
}
}
else
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
lean_dec_ref_known(v_entry_4612_, 1);
lean_dec(v_hint_4588_);
lean_dec(v_mod_4586_);
v___x_4678_ = lean_box(0);
v___x_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
return v___x_4679_;
}
v___jp_4592_:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4604_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
v___x_4605_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4605_, 0, v___y_4603_);
lean_ctor_set(v___x_4605_, 1, v___y_4595_);
lean_ctor_set(v___x_4605_, 2, v___y_4594_);
lean_ctor_set(v___x_4605_, 3, v___y_4601_);
lean_ctor_set(v___x_4605_, 4, v___y_4600_);
lean_ctor_set(v___x_4605_, 5, v___x_4604_);
lean_ctor_set(v___x_4605_, 6, v___y_4593_);
lean_ctor_set(v___x_4605_, 7, v___y_4602_);
lean_ctor_set(v___x_4605_, 8, v___y_4599_);
lean_ctor_set(v___x_4605_, 9, v___y_4597_);
v___x_4606_ = lean_st_ref_put(v___y_4598_, v___x_4605_);
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v___y_4596_);
return v___x_4607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_4680_, lean_object* v_isMeta_4681_, lean_object* v_hint_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
uint8_t v_isMeta_boxed_4686_; lean_object* v_res_4687_; 
v_isMeta_boxed_4686_ = lean_unbox(v_isMeta_4681_);
v_res_4687_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_4680_, v_isMeta_boxed_4686_, v_hint_4682_, v___y_4683_, v___y_4684_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_4688_, lean_object* v_declName_4689_, lean_object* v_as_4690_, size_t v_sz_4691_, size_t v_i_4692_, lean_object* v_b_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
uint8_t v___x_4697_; 
v___x_4697_ = lean_usize_dec_lt(v_i_4692_, v_sz_4691_);
if (v___x_4697_ == 0)
{
lean_object* v___x_4698_; 
lean_dec(v_declName_4689_);
v___x_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4698_, 0, v_b_4693_);
return v___x_4698_;
}
else
{
lean_object* v___x_4699_; lean_object* v_modules_4700_; lean_object* v___x_4701_; lean_object* v_a_4702_; lean_object* v___x_4703_; lean_object* v_toImport_4704_; lean_object* v_module_4705_; lean_object* v___x_4706_; uint8_t v___x_4707_; lean_object* v___x_4708_; 
v___x_4699_ = l_Lean_Environment_header(v___x_4688_);
v_modules_4700_ = lean_ctor_get(v___x_4699_, 3);
lean_inc_ref(v_modules_4700_);
lean_dec_ref(v___x_4699_);
v___x_4701_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4702_ = lean_array_uget_borrowed(v_as_4690_, v_i_4692_);
v___x_4703_ = lean_array_get(v___x_4701_, v_modules_4700_, v_a_4702_);
lean_dec_ref(v_modules_4700_);
v_toImport_4704_ = lean_ctor_get(v___x_4703_, 0);
lean_inc_ref(v_toImport_4704_);
lean_dec(v___x_4703_);
v_module_4705_ = lean_ctor_get(v_toImport_4704_, 0);
lean_inc(v_module_4705_);
lean_dec_ref(v_toImport_4704_);
v___x_4706_ = lean_box(0);
v___x_4707_ = 0;
lean_inc(v_declName_4689_);
v___x_4708_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_4705_, v___x_4707_, v_declName_4689_, v___y_4694_, v___y_4695_);
if (lean_obj_tag(v___x_4708_) == 0)
{
size_t v___x_4709_; size_t v___x_4710_; 
lean_dec_ref_known(v___x_4708_, 1);
v___x_4709_ = ((size_t)1ULL);
v___x_4710_ = lean_usize_add(v_i_4692_, v___x_4709_);
v_i_4692_ = v___x_4710_;
v_b_4693_ = v___x_4706_;
goto _start;
}
else
{
lean_dec(v_declName_4689_);
return v___x_4708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_4712_, lean_object* v_declName_4713_, lean_object* v_as_4714_, lean_object* v_sz_4715_, lean_object* v_i_4716_, lean_object* v_b_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
size_t v_sz_boxed_4721_; size_t v_i_boxed_4722_; lean_object* v_res_4723_; 
v_sz_boxed_4721_ = lean_unbox_usize(v_sz_4715_);
lean_dec(v_sz_4715_);
v_i_boxed_4722_ = lean_unbox_usize(v_i_4716_);
lean_dec(v_i_4716_);
v_res_4723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_4712_, v_declName_4713_, v_as_4714_, v_sz_boxed_4721_, v_i_boxed_4722_, v_b_4717_, v___y_4718_, v___y_4719_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec_ref(v_as_4714_);
lean_dec_ref(v___x_4712_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_4724_, uint8_t v_isMeta_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v_env_4734_; lean_object* v___y_4736_; lean_object* v___x_4749_; 
v___x_4729_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_4730_ = lean_st_ref_get(v___y_4727_);
v_env_4734_ = lean_ctor_get(v___x_4730_, 0);
lean_inc_ref(v_env_4734_);
lean_dec(v___x_4730_);
v___x_4749_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4734_, v_declName_4724_);
if (lean_obj_tag(v___x_4749_) == 0)
{
lean_dec_ref(v_env_4734_);
lean_dec(v_declName_4724_);
goto v___jp_4731_;
}
else
{
lean_object* v_val_4750_; lean_object* v___x_4751_; lean_object* v_modules_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; 
v_val_4750_ = lean_ctor_get(v___x_4749_, 0);
lean_inc(v_val_4750_);
lean_dec_ref_known(v___x_4749_, 1);
v___x_4751_ = l_Lean_Environment_header(v_env_4734_);
v_modules_4752_ = lean_ctor_get(v___x_4751_, 3);
lean_inc_ref(v_modules_4752_);
lean_dec_ref(v___x_4751_);
v___x_4753_ = lean_array_get_size(v_modules_4752_);
v___x_4754_ = lean_nat_dec_lt(v_val_4750_, v___x_4753_);
if (v___x_4754_ == 0)
{
lean_dec_ref(v_modules_4752_);
lean_dec(v_val_4750_);
lean_dec_ref(v_env_4734_);
lean_dec(v_declName_4724_);
goto v___jp_4731_;
}
else
{
lean_object* v___x_4755_; lean_object* v___x_4756_; uint8_t v___y_4758_; 
v___x_4755_ = lean_array_fget(v_modules_4752_, v_val_4750_);
lean_dec(v_val_4750_);
lean_dec_ref(v_modules_4752_);
v___x_4756_ = lean_st_ref_get(v___y_4727_);
if (v_isMeta_4725_ == 0)
{
lean_dec(v___x_4756_);
v___y_4758_ = v_isMeta_4725_;
goto v___jp_4757_;
}
else
{
lean_object* v_env_4769_; uint8_t v___x_4770_; 
v_env_4769_ = lean_ctor_get(v___x_4756_, 0);
lean_inc_ref(v_env_4769_);
lean_dec(v___x_4756_);
lean_inc(v_declName_4724_);
v___x_4770_ = l_Lean_isMarkedMeta(v_env_4769_, v_declName_4724_);
if (v___x_4770_ == 0)
{
v___y_4758_ = v_isMeta_4725_;
goto v___jp_4757_;
}
else
{
uint8_t v___x_4771_; 
v___x_4771_ = 0;
v___y_4758_ = v___x_4771_;
goto v___jp_4757_;
}
}
v___jp_4757_:
{
lean_object* v_toImport_4759_; lean_object* v_module_4760_; lean_object* v___x_4761_; 
v_toImport_4759_ = lean_ctor_get(v___x_4755_, 0);
lean_inc_ref(v_toImport_4759_);
lean_dec(v___x_4755_);
v_module_4760_ = lean_ctor_get(v_toImport_4759_, 0);
lean_inc(v_module_4760_);
lean_dec_ref(v_toImport_4759_);
lean_inc(v_declName_4724_);
v___x_4761_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_4760_, v___y_4758_, v_declName_4724_, v___y_4726_, v___y_4727_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
lean_dec_ref_known(v___x_4761_, 1);
v___x_4762_ = l_Lean_indirectModUseExt;
v___x_4763_ = lean_box(1);
v___x_4764_ = lean_box(0);
lean_inc_ref(v_env_4734_);
v___x_4765_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4729_, v___x_4762_, v_env_4734_, v___x_4763_, v___x_4764_);
v___x_4766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4765_, v_declName_4724_);
lean_dec(v___x_4765_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v___x_4767_; 
v___x_4767_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_4736_ = v___x_4767_;
goto v___jp_4735_;
}
else
{
lean_object* v_val_4768_; 
v_val_4768_ = lean_ctor_get(v___x_4766_, 0);
lean_inc(v_val_4768_);
lean_dec_ref_known(v___x_4766_, 1);
v___y_4736_ = v_val_4768_;
goto v___jp_4735_;
}
}
else
{
lean_dec_ref(v_env_4734_);
lean_dec(v_declName_4724_);
return v___x_4761_;
}
}
}
}
v___jp_4731_:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = lean_box(0);
v___x_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4732_);
return v___x_4733_;
}
v___jp_4735_:
{
lean_object* v___x_4737_; size_t v_sz_4738_; size_t v___x_4739_; lean_object* v___x_4740_; 
v___x_4737_ = lean_box(0);
v_sz_4738_ = lean_array_size(v___y_4736_);
v___x_4739_ = ((size_t)0ULL);
v___x_4740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_4734_, v_declName_4724_, v___y_4736_, v_sz_4738_, v___x_4739_, v___x_4737_, v___y_4726_, v___y_4727_);
lean_dec_ref(v___y_4736_);
lean_dec_ref(v_env_4734_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4747_; 
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4747_ == 0)
{
lean_object* v_unused_4748_; 
v_unused_4748_ = lean_ctor_get(v___x_4740_, 0);
lean_dec(v_unused_4748_);
v___x_4742_ = v___x_4740_;
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
else
{
lean_dec(v___x_4740_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4745_; 
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v___x_4737_);
v___x_4745_ = v___x_4742_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4737_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
else
{
return v___x_4740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_4772_, lean_object* v_isMeta_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
uint8_t v_isMeta_boxed_4777_; lean_object* v_res_4778_; 
v_isMeta_boxed_4777_ = lean_unbox(v_isMeta_4773_);
v_res_4778_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_4772_, v_isMeta_boxed_4777_, v___y_4774_, v___y_4775_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4774_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4783_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4784_ = lean_st_ref_get(v___x_4783_);
v___x_4785_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4784_, v_attrName_4779_);
lean_dec(v___x_4784_);
if (lean_obj_tag(v___x_4785_) == 1)
{
lean_object* v_val_4786_; lean_object* v_ext_4787_; lean_object* v_name_4788_; uint8_t v___x_4789_; lean_object* v___x_4790_; 
v_val_4786_ = lean_ctor_get(v___x_4785_, 0);
v_ext_4787_ = lean_ctor_get(v_val_4786_, 1);
v_name_4788_ = lean_ctor_get(v_ext_4787_, 1);
v___x_4789_ = 1;
lean_inc(v_name_4788_);
v___x_4790_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_4788_, v___x_4789_, v_a_4780_, v_a_4781_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4797_ == 0)
{
lean_object* v_unused_4798_; 
v_unused_4798_ = lean_ctor_get(v___x_4790_, 0);
lean_dec(v_unused_4798_);
v___x_4792_ = v___x_4790_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_dec(v___x_4790_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 0, v___x_4785_);
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v___x_4785_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
else
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
lean_dec_ref_known(v___x_4785_, 1);
v_a_4799_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4790_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4790_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4804_; 
if (v_isShared_4802_ == 0)
{
v___x_4804_ = v___x_4801_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
}
else
{
lean_object* v___x_4807_; 
v___x_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4785_);
return v___x_4807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_4808_, v_a_4809_, v_a_4810_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
lean_dec(v_attrName_4808_);
return v_res_4812_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_4813_; 
v___x_4813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_4814_, lean_object* v_x_4815_){
_start:
{
if (lean_obj_tag(v_x_4815_) == 0)
{
return v_x_4814_;
}
else
{
lean_object* v_key_4816_; lean_object* v_value_4817_; lean_object* v_tail_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4844_; 
v_key_4816_ = lean_ctor_get(v_x_4815_, 0);
v_value_4817_ = lean_ctor_get(v_x_4815_, 1);
v_tail_4818_ = lean_ctor_get(v_x_4815_, 2);
v_isSharedCheck_4844_ = !lean_is_exclusive(v_x_4815_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4820_ = v_x_4815_;
v_isShared_4821_ = v_isSharedCheck_4844_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_tail_4818_);
lean_inc(v_value_4817_);
lean_inc(v_key_4816_);
lean_dec(v_x_4815_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4844_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; uint64_t v___y_4824_; 
v___x_4822_ = lean_array_get_size(v_x_4814_);
if (lean_obj_tag(v_key_4816_) == 0)
{
uint64_t v___x_4842_; 
v___x_4842_ = 1723ULL;
v___y_4824_ = v___x_4842_;
goto v___jp_4823_;
}
else
{
uint64_t v_hash_4843_; 
v_hash_4843_ = lean_ctor_get_uint64(v_key_4816_, sizeof(void*)*2);
v___y_4824_ = v_hash_4843_;
goto v___jp_4823_;
}
v___jp_4823_:
{
uint64_t v___x_4825_; uint64_t v___x_4826_; uint64_t v_fold_4827_; uint64_t v___x_4828_; uint64_t v___x_4829_; uint64_t v___x_4830_; size_t v___x_4831_; size_t v___x_4832_; size_t v___x_4833_; size_t v___x_4834_; size_t v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4825_ = 32ULL;
v___x_4826_ = lean_uint64_shift_right(v___y_4824_, v___x_4825_);
v_fold_4827_ = lean_uint64_xor(v___y_4824_, v___x_4826_);
v___x_4828_ = 16ULL;
v___x_4829_ = lean_uint64_shift_right(v_fold_4827_, v___x_4828_);
v___x_4830_ = lean_uint64_xor(v_fold_4827_, v___x_4829_);
v___x_4831_ = lean_uint64_to_usize(v___x_4830_);
v___x_4832_ = lean_usize_of_nat(v___x_4822_);
v___x_4833_ = ((size_t)1ULL);
v___x_4834_ = lean_usize_sub(v___x_4832_, v___x_4833_);
v___x_4835_ = lean_usize_land(v___x_4831_, v___x_4834_);
v___x_4836_ = lean_array_uget_borrowed(v_x_4814_, v___x_4835_);
lean_inc(v___x_4836_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 2, v___x_4836_);
v___x_4838_ = v___x_4820_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_key_4816_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v_value_4817_);
lean_ctor_set(v_reuseFailAlloc_4841_, 2, v___x_4836_);
v___x_4838_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
lean_object* v___x_4839_; 
v___x_4839_ = lean_array_uset(v_x_4814_, v___x_4835_, v___x_4838_);
v_x_4814_ = v___x_4839_;
v_x_4815_ = v_tail_4818_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4845_, lean_object* v_source_4846_, lean_object* v_target_4847_){
_start:
{
lean_object* v___x_4848_; uint8_t v___x_4849_; 
v___x_4848_ = lean_array_get_size(v_source_4846_);
v___x_4849_ = lean_nat_dec_lt(v_i_4845_, v___x_4848_);
if (v___x_4849_ == 0)
{
lean_dec_ref(v_source_4846_);
lean_dec(v_i_4845_);
return v_target_4847_;
}
else
{
lean_object* v_es_4850_; lean_object* v___x_4851_; lean_object* v_source_4852_; lean_object* v_target_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v_es_4850_ = lean_array_fget(v_source_4846_, v_i_4845_);
v___x_4851_ = lean_box(0);
v_source_4852_ = lean_array_fset(v_source_4846_, v_i_4845_, v___x_4851_);
v_target_4853_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_4847_, v_es_4850_);
v___x_4854_ = lean_unsigned_to_nat(1u);
v___x_4855_ = lean_nat_add(v_i_4845_, v___x_4854_);
lean_dec(v_i_4845_);
v_i_4845_ = v___x_4855_;
v_source_4846_ = v_source_4852_;
v_target_4847_ = v_target_4853_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_4857_){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v_nbuckets_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4858_ = lean_array_get_size(v_data_4857_);
v___x_4859_ = lean_unsigned_to_nat(2u);
v_nbuckets_4860_ = lean_nat_mul(v___x_4858_, v___x_4859_);
v___x_4861_ = lean_unsigned_to_nat(0u);
v___x_4862_ = lean_box(0);
v___x_4863_ = lean_mk_array(v_nbuckets_4860_, v___x_4862_);
v___x_4864_ = lean_array_propagate_mark(v_data_4857_, v___x_4863_);
v___x_4865_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_4861_, v_data_4857_, v___x_4864_);
return v___x_4865_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_4866_, lean_object* v_x_4867_){
_start:
{
if (lean_obj_tag(v_x_4867_) == 0)
{
uint8_t v___x_4868_; 
v___x_4868_ = 0;
return v___x_4868_;
}
else
{
lean_object* v_key_4869_; lean_object* v_tail_4870_; uint8_t v___x_4871_; 
v_key_4869_ = lean_ctor_get(v_x_4867_, 0);
v_tail_4870_ = lean_ctor_get(v_x_4867_, 2);
v___x_4871_ = lean_name_eq(v_key_4869_, v_a_4866_);
if (v___x_4871_ == 0)
{
v_x_4867_ = v_tail_4870_;
goto _start;
}
else
{
return v___x_4871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_4873_, lean_object* v_x_4874_){
_start:
{
uint8_t v_res_4875_; lean_object* v_r_4876_; 
v_res_4875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4873_, v_x_4874_);
lean_dec(v_x_4874_);
lean_dec(v_a_4873_);
v_r_4876_ = lean_box(v_res_4875_);
return v_r_4876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_4877_, lean_object* v_b_4878_, lean_object* v_x_4879_){
_start:
{
if (lean_obj_tag(v_x_4879_) == 0)
{
lean_dec(v_b_4878_);
lean_dec(v_a_4877_);
return v_x_4879_;
}
else
{
lean_object* v_key_4880_; lean_object* v_value_4881_; lean_object* v_tail_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4894_; 
v_key_4880_ = lean_ctor_get(v_x_4879_, 0);
v_value_4881_ = lean_ctor_get(v_x_4879_, 1);
v_tail_4882_ = lean_ctor_get(v_x_4879_, 2);
v_isSharedCheck_4894_ = !lean_is_exclusive(v_x_4879_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4884_ = v_x_4879_;
v_isShared_4885_ = v_isSharedCheck_4894_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_tail_4882_);
lean_inc(v_value_4881_);
lean_inc(v_key_4880_);
lean_dec(v_x_4879_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4894_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
uint8_t v___x_4886_; 
v___x_4886_ = lean_name_eq(v_key_4880_, v_a_4877_);
if (v___x_4886_ == 0)
{
lean_object* v___x_4887_; lean_object* v___x_4889_; 
v___x_4887_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4877_, v_b_4878_, v_tail_4882_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 2, v___x_4887_);
v___x_4889_ = v___x_4884_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_key_4880_);
lean_ctor_set(v_reuseFailAlloc_4890_, 1, v_value_4881_);
lean_ctor_set(v_reuseFailAlloc_4890_, 2, v___x_4887_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
else
{
lean_object* v___x_4892_; 
lean_dec(v_value_4881_);
lean_dec(v_key_4880_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 1, v_b_4878_);
lean_ctor_set(v___x_4884_, 0, v_a_4877_);
v___x_4892_ = v___x_4884_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4877_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v_b_4878_);
lean_ctor_set(v_reuseFailAlloc_4893_, 2, v_tail_4882_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_4895_, lean_object* v_a_4896_, lean_object* v_b_4897_){
_start:
{
lean_object* v_size_4898_; lean_object* v_buckets_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4945_; 
v_size_4898_ = lean_ctor_get(v_m_4895_, 0);
v_buckets_4899_ = lean_ctor_get(v_m_4895_, 1);
v_isSharedCheck_4945_ = !lean_is_exclusive(v_m_4895_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4901_ = v_m_4895_;
v_isShared_4902_ = v_isSharedCheck_4945_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_buckets_4899_);
lean_inc(v_size_4898_);
lean_dec(v_m_4895_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4945_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; uint64_t v___y_4905_; 
v___x_4903_ = lean_array_get_size(v_buckets_4899_);
if (lean_obj_tag(v_a_4896_) == 0)
{
uint64_t v___x_4943_; 
v___x_4943_ = 1723ULL;
v___y_4905_ = v___x_4943_;
goto v___jp_4904_;
}
else
{
uint64_t v_hash_4944_; 
v_hash_4944_ = lean_ctor_get_uint64(v_a_4896_, sizeof(void*)*2);
v___y_4905_ = v_hash_4944_;
goto v___jp_4904_;
}
v___jp_4904_:
{
uint64_t v___x_4906_; uint64_t v___x_4907_; uint64_t v_fold_4908_; uint64_t v___x_4909_; uint64_t v___x_4910_; uint64_t v___x_4911_; size_t v___x_4912_; size_t v___x_4913_; size_t v___x_4914_; size_t v___x_4915_; size_t v___x_4916_; lean_object* v_bkt_4917_; uint8_t v___x_4918_; 
v___x_4906_ = 32ULL;
v___x_4907_ = lean_uint64_shift_right(v___y_4905_, v___x_4906_);
v_fold_4908_ = lean_uint64_xor(v___y_4905_, v___x_4907_);
v___x_4909_ = 16ULL;
v___x_4910_ = lean_uint64_shift_right(v_fold_4908_, v___x_4909_);
v___x_4911_ = lean_uint64_xor(v_fold_4908_, v___x_4910_);
v___x_4912_ = lean_uint64_to_usize(v___x_4911_);
v___x_4913_ = lean_usize_of_nat(v___x_4903_);
v___x_4914_ = ((size_t)1ULL);
v___x_4915_ = lean_usize_sub(v___x_4913_, v___x_4914_);
v___x_4916_ = lean_usize_land(v___x_4912_, v___x_4915_);
v_bkt_4917_ = lean_array_uget_borrowed(v_buckets_4899_, v___x_4916_);
v___x_4918_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4896_, v_bkt_4917_);
if (v___x_4918_ == 0)
{
lean_object* v___x_4919_; lean_object* v_size_x27_4920_; lean_object* v___x_4921_; lean_object* v_buckets_x27_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; uint8_t v___x_4928_; 
v___x_4919_ = lean_unsigned_to_nat(1u);
v_size_x27_4920_ = lean_nat_add(v_size_4898_, v___x_4919_);
lean_dec(v_size_4898_);
lean_inc(v_bkt_4917_);
v___x_4921_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4921_, 0, v_a_4896_);
lean_ctor_set(v___x_4921_, 1, v_b_4897_);
lean_ctor_set(v___x_4921_, 2, v_bkt_4917_);
v_buckets_x27_4922_ = lean_array_uset(v_buckets_4899_, v___x_4916_, v___x_4921_);
v___x_4923_ = lean_unsigned_to_nat(4u);
v___x_4924_ = lean_nat_mul(v_size_x27_4920_, v___x_4923_);
v___x_4925_ = lean_unsigned_to_nat(3u);
v___x_4926_ = lean_nat_div(v___x_4924_, v___x_4925_);
lean_dec(v___x_4924_);
v___x_4927_ = lean_array_get_size(v_buckets_x27_4922_);
v___x_4928_ = lean_nat_dec_le(v___x_4926_, v___x_4927_);
lean_dec(v___x_4926_);
if (v___x_4928_ == 0)
{
lean_object* v_val_4929_; lean_object* v___x_4931_; 
v_val_4929_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_4922_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 1, v_val_4929_);
lean_ctor_set(v___x_4901_, 0, v_size_x27_4920_);
v___x_4931_ = v___x_4901_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_size_x27_4920_);
lean_ctor_set(v_reuseFailAlloc_4932_, 1, v_val_4929_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
else
{
lean_object* v___x_4934_; 
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 1, v_buckets_x27_4922_);
lean_ctor_set(v___x_4901_, 0, v_size_x27_4920_);
v___x_4934_ = v___x_4901_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_size_x27_4920_);
lean_ctor_set(v_reuseFailAlloc_4935_, 1, v_buckets_x27_4922_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
else
{
lean_object* v___x_4936_; lean_object* v_buckets_x27_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4941_; 
lean_inc(v_bkt_4917_);
v___x_4936_ = lean_box(0);
v_buckets_x27_4937_ = lean_array_uset(v_buckets_4899_, v___x_4916_, v___x_4936_);
v___x_4938_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4896_, v_b_4897_, v_bkt_4917_);
v___x_4939_ = lean_array_uset(v_buckets_x27_4937_, v___x_4916_, v___x_4938_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 1, v___x_4939_);
v___x_4941_ = v___x_4901_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_size_4898_);
lean_ctor_set(v_reuseFailAlloc_4942_, 1, v___x_4939_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_4946_, lean_object* v_ref_4947_){
_start:
{
lean_object* v___x_4949_; 
lean_inc(v_ref_4947_);
v___x_4949_ = l_Lean_Meta_Grind_mkExtension(v_ref_4947_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; uint8_t v___x_4951_; uint8_t v___x_4952_; lean_object* v___x_4953_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc_n(v_a_4950_, 2);
lean_dec_ref_known(v___x_4949_, 1);
v___x_4951_ = 0;
v___x_4952_ = 1;
lean_inc(v_ref_4947_);
lean_inc(v_attrName_4946_);
v___x_4953_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4946_, v___x_4951_, v___x_4952_, v_a_4950_, v_ref_4947_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v___x_4954_; 
lean_dec_ref_known(v___x_4953_, 1);
lean_inc(v_ref_4947_);
lean_inc(v_a_4950_);
lean_inc(v_attrName_4946_);
v___x_4954_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4946_, v___x_4951_, v___x_4951_, v_a_4950_, v_ref_4947_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v___x_4955_; 
lean_dec_ref_known(v___x_4954_, 1);
lean_inc(v_ref_4947_);
lean_inc(v_a_4950_);
lean_inc(v_attrName_4946_);
v___x_4955_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4946_, v___x_4952_, v___x_4952_, v_a_4950_, v_ref_4947_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v___x_4956_; 
lean_dec_ref_known(v___x_4955_, 1);
lean_inc(v_a_4950_);
lean_inc(v_attrName_4946_);
v___x_4956_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4946_, v___x_4952_, v___x_4951_, v_a_4950_, v_ref_4947_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4967_; 
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4967_ == 0)
{
lean_object* v_unused_4968_; 
v_unused_4968_ = lean_ctor_get(v___x_4956_, 0);
lean_dec(v_unused_4968_);
v___x_4958_ = v___x_4956_;
v_isShared_4959_ = v_isSharedCheck_4967_;
goto v_resetjp_4957_;
}
else
{
lean_dec(v___x_4956_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4967_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4965_; 
v___x_4960_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4961_ = lean_st_ref_take(v___x_4960_);
lean_inc(v_a_4950_);
v___x_4962_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_4961_, v_attrName_4946_, v_a_4950_);
v___x_4963_ = lean_st_ref_put(v___x_4960_, v___x_4962_);
if (v_isShared_4959_ == 0)
{
lean_ctor_set(v___x_4958_, 0, v_a_4950_);
v___x_4965_ = v___x_4958_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_a_4950_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
else
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_dec(v_a_4950_);
lean_dec(v_attrName_4946_);
v_a_4969_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4956_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4956_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
lean_dec(v_a_4950_);
lean_dec(v_ref_4947_);
lean_dec(v_attrName_4946_);
v_a_4977_ = lean_ctor_get(v___x_4955_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4979_ = v___x_4955_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4955_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4982_; 
if (v_isShared_4980_ == 0)
{
v___x_4982_ = v___x_4979_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4977_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
}
else
{
lean_object* v_a_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4992_; 
lean_dec(v_a_4950_);
lean_dec(v_ref_4947_);
lean_dec(v_attrName_4946_);
v_a_4985_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4987_ = v___x_4954_;
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4954_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4990_; 
if (v_isShared_4988_ == 0)
{
v___x_4990_ = v___x_4987_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
}
else
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5000_; 
lean_dec(v_a_4950_);
lean_dec(v_ref_4947_);
lean_dec(v_attrName_4946_);
v_a_4993_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4953_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4953_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
else
{
lean_dec(v_ref_4947_);
lean_dec(v_attrName_4946_);
return v___x_4949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_5001_, lean_object* v_ref_5002_, lean_object* v_a_5003_){
_start:
{
lean_object* v_res_5004_; 
v_res_5004_ = l_Lean_Meta_Grind_registerAttr(v_attrName_5001_, v_ref_5002_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_5005_, lean_object* v_m_5006_, lean_object* v_a_5007_, lean_object* v_b_5008_){
_start:
{
lean_object* v___x_5009_; 
v___x_5009_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_5006_, v_a_5007_, v_b_5008_);
return v___x_5009_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_5010_, lean_object* v_a_5011_, lean_object* v_x_5012_){
_start:
{
uint8_t v___x_5013_; 
v___x_5013_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_5011_, v_x_5012_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5014_, lean_object* v_a_5015_, lean_object* v_x_5016_){
_start:
{
uint8_t v_res_5017_; lean_object* v_r_5018_; 
v_res_5017_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_5014_, v_a_5015_, v_x_5016_);
lean_dec(v_x_5016_);
lean_dec(v_a_5015_);
v_r_5018_ = lean_box(v_res_5017_);
return v_r_5018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_5019_, lean_object* v_data_5020_){
_start:
{
lean_object* v___x_5021_; 
v___x_5021_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_5020_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_5022_, lean_object* v_a_5023_, lean_object* v_b_5024_, lean_object* v_x_5025_){
_start:
{
lean_object* v___x_5026_; 
v___x_5026_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_5023_, v_b_5024_, v_x_5025_);
return v___x_5026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5027_, lean_object* v_i_5028_, lean_object* v_source_5029_, lean_object* v_target_5030_){
_start:
{
lean_object* v___x_5031_; 
v___x_5031_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_5028_, v_source_5029_, v_target_5030_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_5032_, lean_object* v_x_5033_, lean_object* v_x_5034_){
_start:
{
lean_object* v___x_5035_; 
v___x_5035_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_5033_, v_x_5034_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_5043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_5044_ = l_Lean_Meta_Grind_registerAttr(v___x_5042_, v___x_5043_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_5058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_5059_ = l_Lean_Meta_Grind_registerAttr(v___x_5057_, v___x_5058_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_5062_, lean_object* v_a_5063_){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v_env_5067_; lean_object* v___x_5068_; lean_object* v_ext_5069_; lean_object* v_toEnvExtension_5070_; lean_object* v_asyncMode_5071_; uint8_t v___x_5072_; lean_object* v___x_5073_; lean_object* v_casesTypes_5074_; uint8_t v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5065_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_5066_ = lean_st_ref_get(v_a_5063_);
v_env_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc_ref(v_env_5067_);
lean_dec(v___x_5066_);
v___x_5068_ = l_Lean_Meta_Grind_grindExt;
v_ext_5069_ = lean_ctor_get(v___x_5068_, 1);
v_toEnvExtension_5070_ = lean_ctor_get(v_ext_5069_, 0);
v_asyncMode_5071_ = lean_ctor_get(v_toEnvExtension_5070_, 2);
v___x_5072_ = 0;
v___x_5073_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5065_, v___x_5068_, v_env_5067_, v_asyncMode_5071_, v___x_5072_);
v_casesTypes_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc_ref(v_casesTypes_5074_);
lean_dec(v___x_5073_);
v___x_5075_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_5074_, v_declName_5062_);
lean_dec_ref(v_casesTypes_5074_);
v___x_5076_ = lean_box(v___x_5075_);
v___x_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5076_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_){
_start:
{
lean_object* v_res_5081_; 
v_res_5081_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_5078_, v_a_5079_);
lean_dec(v_a_5079_);
lean_dec(v_declName_5078_);
return v_res_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v___x_5086_; 
v___x_5086_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_5082_, v_a_5084_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_5087_, v_a_5088_, v_a_5089_);
lean_dec(v_a_5089_);
lean_dec_ref(v_a_5088_);
lean_dec(v_declName_5087_);
return v_res_5091_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default = _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default);
l_Lean_Meta_Grind_instInhabitedNormSymTheorems = _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymTheorems);
l_Lean_Meta_Grind_instInhabitedNormSymEntry_default = _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymEntry_default);
l_Lean_Meta_Grind_instInhabitedNormSymEntry = _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymEntry);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normSymExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normSymExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_extensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_extensionMapRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_grindExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_grindExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_liaExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_liaExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1 = _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1);
l_Lean_Meta_Grind_registerAttr___auto__1 = _init_l_Lean_Meta_Grind_registerAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_Grind_registerAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
