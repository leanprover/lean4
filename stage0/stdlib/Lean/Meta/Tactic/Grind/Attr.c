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
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_addEntry(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
lean_object* l_Lean_registerAutomationAttr(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "normSymExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 33, 18, 12, 138, 185, 216, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_NormSymTheorems_addEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_;
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object* v___y_216_){
_start:
{
lean_inc_ref(v___y_216_);
return v___y_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(v___y_217_);
lean_dec_ref(v___y_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object* v_x_219_, lean_object* v_a_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v_a_220_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v_x_224_, lean_object* v_a_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(v_x_224_, v_a_225_, v___y_226_);
lean_dec_ref(v___y_226_);
lean_dec_ref(v_x_224_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object* v_x_229_, lean_object* v_e_230_){
_start:
{
lean_object* v___x_231_; 
lean_inc_ref(v_e_230_);
v___x_231_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_NormSymEntry_declName_x3f(v_e_230_);
if (lean_obj_tag(v___x_231_) == 1)
{
lean_object* v_val_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_246_; 
v_val_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_246_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_246_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_val_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_246_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
uint8_t v___x_236_; 
v___x_236_ = l_Lean_isPrivateName(v_val_232_);
lean_dec(v_val_232_);
if (v___x_236_ == 0)
{
lean_object* v___x_238_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v_e_230_);
v___x_238_ = v___x_234_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_e_230_);
v___x_238_ = v_reuseFailAlloc_240_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; 
lean_inc_ref_n(v___x_238_, 2);
v___x_239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
lean_ctor_set(v___x_239_, 2, v___x_238_);
return v___x_239_;
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_241_ = lean_box(0);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v_e_230_);
v___x_243_ = v___x_234_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_e_230_);
v___x_243_ = v_reuseFailAlloc_245_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_244_, 0, v___x_241_);
lean_ctor_set(v___x_244_, 1, v___x_241_);
lean_ctor_set(v___x_244_, 2, v___x_243_);
return v___x_244_;
}
}
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v___x_231_);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v_e_230_);
lean_inc_ref_n(v___x_247_, 2);
v___x_248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
lean_ctor_set(v___x_248_, 2, v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v_x_249_, lean_object* v_e_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(v_x_249_, v_e_250_);
lean_dec_ref(v_x_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object* v___x_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v___x_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(v___x_255_);
return v_res_257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_268_; lean_object* v___f_269_; 
v___x_268_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4);
v___f_269_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_269_, 0, v___x_268_);
return v___f_269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_270_; lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___x_273_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___f_271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___f_272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_);
v___x_273_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedGlobals___boxed), 9, 6);
lean_closure_set(v___x_273_, 0, lean_box(0));
lean_closure_set(v___x_273_, 1, lean_box(0));
lean_closure_set(v___x_273_, 2, lean_box(0));
lean_closure_set(v___x_273_, 3, v___f_272_);
lean_closure_set(v___x_273_, 4, v___f_271_);
lean_closure_set(v___x_273_, 5, v___x_270_);
return v___x_273_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_274_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_);
v___x_275_ = lean_box(0);
v___x_276_ = 0;
v___f_277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___f_278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_279_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4);
v___x_280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_282_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
lean_ctor_set(v___x_282_, 2, v___x_280_);
lean_ctor_set(v___x_282_, 3, v___x_279_);
lean_ctor_set(v___x_282_, 4, v___f_278_);
lean_ctor_set(v___x_282_, 5, v___f_277_);
lean_ctor_set(v___x_282_, 6, v___x_275_);
lean_ctor_set(v___x_282_, 7, v___x_274_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*8, v___x_276_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*8 + 1, v___x_276_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_);
v___x_285_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_();
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(lean_object* v_____r_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0));
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___boxed(lean_object* v_____r_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v_____r_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(lean_object* v_msgData_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v_env_312_; uint8_t v___x_313_; lean_object* v_env_314_; lean_object* v___x_315_; lean_object* v_toCold_316_; lean_object* v_mctx_317_; lean_object* v_lctx_318_; lean_object* v_options_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_311_ = lean_st_ref_get(v___y_309_);
v_env_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_env_312_);
lean_dec(v___x_311_);
v___x_313_ = 0;
v_env_314_ = l_Lean_Environment_setRecordingDeps(v_env_312_, v___x_313_);
v___x_315_ = lean_st_ref_get(v___y_307_);
v_toCold_316_ = lean_ctor_get(v___y_308_, 0);
v_mctx_317_ = lean_ctor_get(v___x_315_, 0);
lean_inc_ref(v_mctx_317_);
lean_dec(v___x_315_);
v_lctx_318_ = lean_ctor_get(v___y_306_, 2);
v_options_319_ = lean_ctor_get(v_toCold_316_, 2);
lean_inc_ref(v_options_319_);
lean_inc_ref(v_lctx_318_);
v___x_320_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_320_, 0, v_env_314_);
lean_ctor_set(v___x_320_, 1, v_mctx_317_);
lean_ctor_set(v___x_320_, 2, v_lctx_318_);
lean_ctor_set(v___x_320_, 3, v_options_319_);
v___x_321_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_msgData_305_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msgData_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
return v_res_329_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_330_; double v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_float_of_nat(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(lean_object* v_cls_335_, lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_ref_342_; lean_object* v___x_343_; lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_389_; 
v_ref_342_ = lean_ctor_get(v___y_339_, 2);
v___x_343_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msg_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_389_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_389_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_389_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v_traceState_349_; lean_object* v_env_350_; lean_object* v_nextMacroScope_351_; lean_object* v_ngen_352_; lean_object* v_auxDeclNGen_353_; lean_object* v_cache_354_; lean_object* v_recordedDeps_355_; lean_object* v_messages_356_; lean_object* v_infoState_357_; lean_object* v_snapshotTasks_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_388_; 
v___x_348_ = lean_st_ref_take(v___y_340_);
v_traceState_349_ = lean_ctor_get(v___x_348_, 4);
v_env_350_ = lean_ctor_get(v___x_348_, 0);
v_nextMacroScope_351_ = lean_ctor_get(v___x_348_, 1);
v_ngen_352_ = lean_ctor_get(v___x_348_, 2);
v_auxDeclNGen_353_ = lean_ctor_get(v___x_348_, 3);
v_cache_354_ = lean_ctor_get(v___x_348_, 5);
v_recordedDeps_355_ = lean_ctor_get(v___x_348_, 6);
v_messages_356_ = lean_ctor_get(v___x_348_, 7);
v_infoState_357_ = lean_ctor_get(v___x_348_, 8);
v_snapshotTasks_358_ = lean_ctor_get(v___x_348_, 9);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_388_ == 0)
{
v___x_360_ = v___x_348_;
v_isShared_361_ = v_isSharedCheck_388_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_snapshotTasks_358_);
lean_inc(v_infoState_357_);
lean_inc(v_messages_356_);
lean_inc(v_recordedDeps_355_);
lean_inc(v_cache_354_);
lean_inc(v_traceState_349_);
lean_inc(v_auxDeclNGen_353_);
lean_inc(v_ngen_352_);
lean_inc(v_nextMacroScope_351_);
lean_inc(v_env_350_);
lean_dec(v___x_348_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_388_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
uint64_t v_tid_362_; lean_object* v_traces_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_387_; 
v_tid_362_ = lean_ctor_get_uint64(v_traceState_349_, sizeof(void*)*1);
v_traces_363_ = lean_ctor_get(v_traceState_349_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_traceState_349_);
if (v_isSharedCheck_387_ == 0)
{
v___x_365_ = v_traceState_349_;
v_isShared_366_ = v_isSharedCheck_387_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_traces_363_);
lean_dec(v_traceState_349_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_387_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; double v___x_369_; uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_367_ = lean_box(0);
v___x_368_ = lean_box(0);
v___x_369_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0);
v___x_370_ = 0;
v___x_371_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_372_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_372_, 0, v_cls_335_);
lean_ctor_set(v___x_372_, 1, v___x_368_);
lean_ctor_set(v___x_372_, 2, v___x_371_);
lean_ctor_set_float(v___x_372_, sizeof(void*)*3, v___x_369_);
lean_ctor_set_float(v___x_372_, sizeof(void*)*3 + 8, v___x_369_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*3 + 16, v___x_370_);
v___x_373_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2));
v___x_374_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v_a_344_);
lean_ctor_set(v___x_374_, 2, v___x_373_);
lean_inc(v_ref_342_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_ref_342_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = l_Lean_PersistentArray_push___redArg(v_traces_363_, v___x_375_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_376_);
v___x_378_ = v___x_365_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_376_);
lean_ctor_set_uint64(v_reuseFailAlloc_386_, sizeof(void*)*1, v_tid_362_);
v___x_378_ = v_reuseFailAlloc_386_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 4, v___x_378_);
v___x_380_ = v___x_360_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_env_350_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_nextMacroScope_351_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_ngen_352_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v_auxDeclNGen_353_);
lean_ctor_set(v_reuseFailAlloc_385_, 4, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_385_, 5, v_cache_354_);
lean_ctor_set(v_reuseFailAlloc_385_, 6, v_recordedDeps_355_);
lean_ctor_set(v_reuseFailAlloc_385_, 7, v_messages_356_);
lean_ctor_set(v_reuseFailAlloc_385_, 8, v_infoState_357_);
lean_ctor_set(v_reuseFailAlloc_385_, 9, v_snapshotTasks_358_);
v___x_380_ = v_reuseFailAlloc_385_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = lean_st_ref_put(v___y_340_, v___x_380_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_367_);
v___x_383_ = v___x_346_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_367_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___boxed(lean_object* v_cls_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_390_, v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1));
v___x_403_ = l_Lean_Name_append(v___x_402_, v___x_401_);
return v___x_403_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(lean_object* v_thm_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___y_420_; lean_object* v_proof_433_; 
v_proof_433_ = lean_ctor_get(v_thm_413_, 2);
if (lean_obj_tag(v_proof_433_) == 4)
{
lean_object* v_declName_434_; lean_object* v___x_438_; 
lean_inc_ref(v_proof_433_);
lean_dec_ref(v_thm_413_);
v_declName_434_ = lean_ctor_get(v_proof_433_, 0);
lean_inc_n(v_declName_434_, 2);
lean_dec_ref_known(v_proof_433_, 2);
v___x_438_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_434_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_447_; 
lean_dec(v_declName_434_);
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_447_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v_a_439_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_443_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_485_; 
v_a_448_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_485_ == 0)
{
v___x_450_ = v___x_438_;
v_isShared_451_ = v_isSharedCheck_485_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_438_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_485_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
uint8_t v___x_452_; 
v___x_452_ = l_Lean_Exception_isInterrupt(v_a_448_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; 
lean_inc(v_a_448_);
v___x_453_ = l_Lean_Exception_isRuntime(v_a_448_);
if (v___x_453_ == 0)
{
lean_object* v_toCold_454_; lean_object* v_options_455_; uint8_t v_hasTrace_456_; 
lean_del_object(v___x_450_);
v_toCold_454_ = lean_ctor_get(v_a_416_, 0);
v_options_455_ = lean_ctor_get(v_toCold_454_, 2);
v_hasTrace_456_ = lean_ctor_get_uint8(v_options_455_, sizeof(void*)*1);
if (v_hasTrace_456_ == 0)
{
lean_dec(v_a_448_);
lean_dec(v_declName_434_);
goto v___jp_435_;
}
else
{
lean_object* v_inheritedTraceOptions_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_inheritedTraceOptions_457_ = lean_ctor_get(v_toCold_454_, 11);
v___x_458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_460_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_457_, v_options_455_, v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v_a_448_);
lean_dec(v_declName_434_);
goto v___jp_435_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_461_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4);
v___x_462_ = l_Lean_MessageData_ofConstName(v_declName_434_, v___x_453_);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_Exception_toMessageData(v_a_448_);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v___x_458_, v___x_467_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v_a_469_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
v___y_420_ = v___x_470_;
goto v___jp_419_;
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_471_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_468_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_468_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v_declName_434_);
if (v_isShared_451_ == 0)
{
v___x_480_ = v___x_450_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_448_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v___x_483_; 
lean_dec(v_declName_434_);
if (v_isShared_451_ == 0)
{
v___x_483_ = v___x_450_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_448_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
v___jp_435_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_box(0);
v___x_437_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v___x_436_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
v___y_420_ = v___x_437_;
goto v___jp_419_;
}
}
else
{
lean_object* v_toCold_486_; lean_object* v_options_487_; uint8_t v_hasTrace_488_; 
v_toCold_486_ = lean_ctor_get(v_a_416_, 0);
v_options_487_ = lean_ctor_get(v_toCold_486_, 2);
v_hasTrace_488_ = lean_ctor_get_uint8(v_options_487_, sizeof(void*)*1);
if (v_hasTrace_488_ == 0)
{
lean_dec_ref(v_thm_413_);
goto v___jp_430_;
}
else
{
lean_object* v_origin_489_; lean_object* v_inheritedTraceOptions_490_; lean_object* v_cls_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_origin_489_ = lean_ctor_get(v_thm_413_, 4);
lean_inc_ref(v_origin_489_);
lean_dec_ref(v_thm_413_);
v_inheritedTraceOptions_490_ = lean_ctor_get(v_toCold_486_, 11);
v_cls_491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_492_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_493_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_490_, v_options_487_, v___x_492_);
if (v___x_493_ == 0)
{
lean_dec_ref(v_origin_489_);
goto v___jp_430_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_494_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4);
v___x_495_ = l_Lean_Meta_Origin_key(v_origin_489_);
lean_dec_ref(v_origin_489_);
v___x_496_ = l_Lean_MessageData_ofName(v___x_495_);
v___x_497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_494_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_491_, v___x_499_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_dec_ref_known(v___x_500_, 1);
goto v___jp_430_;
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
v___jp_419_:
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
v_a_421_ = lean_ctor_get(v___y_420_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___y_420_);
if (v_isSharedCheck_429_ == 0)
{
v___x_423_ = v___y_420_;
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___y_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_a_425_; lean_object* v___x_427_; 
v_a_425_ = lean_ctor_get(v_a_421_, 0);
lean_inc(v_a_425_);
lean_dec(v_a_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v_a_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
v___jp_430_:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___boxed(lean_object* v_thm_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(v_thm_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
return v_res_515_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___dummy_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg();
return v_res_521_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg();
return v___x_526_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0);
v___x_531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
lean_ctor_set(v___x_531_, 2, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_532_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__4);
v___x_533_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3);
v___x_534_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0);
v___x_535_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
v___x_536_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_534_);
lean_ctor_set(v___x_536_, 2, v___x_533_);
lean_ctor_set(v___x_536_, 3, v___x_534_);
lean_ctor_set(v___x_536_, 4, v___x_534_);
lean_ctor_set(v___x_536_, 5, v___x_534_);
lean_ctor_set(v___x_536_, 6, v___x_534_);
lean_ctor_set(v___x_536_, 7, v___x_532_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(lean_object* v_ext_537_, lean_object* v_b_538_, uint8_t v_kind_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_toCold_544_; lean_object* v_currNamespace_545_; lean_object* v___x_546_; lean_object* v_env_547_; lean_object* v_nextMacroScope_548_; lean_object* v_ngen_549_; lean_object* v_auxDeclNGen_550_; lean_object* v_traceState_551_; lean_object* v_recordedDeps_552_; lean_object* v_messages_553_; lean_object* v_infoState_554_; lean_object* v_snapshotTasks_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_582_; 
v_toCold_544_ = lean_ctor_get(v___y_541_, 0);
v_currNamespace_545_ = lean_ctor_get(v_toCold_544_, 4);
v___x_546_ = lean_st_ref_take(v___y_542_);
v_env_547_ = lean_ctor_get(v___x_546_, 0);
v_nextMacroScope_548_ = lean_ctor_get(v___x_546_, 1);
v_ngen_549_ = lean_ctor_get(v___x_546_, 2);
v_auxDeclNGen_550_ = lean_ctor_get(v___x_546_, 3);
v_traceState_551_ = lean_ctor_get(v___x_546_, 4);
v_recordedDeps_552_ = lean_ctor_get(v___x_546_, 6);
v_messages_553_ = lean_ctor_get(v___x_546_, 7);
v_infoState_554_ = lean_ctor_get(v___x_546_, 8);
v_snapshotTasks_555_ = lean_ctor_get(v___x_546_, 9);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v___x_546_, 5);
lean_dec(v_unused_583_);
v___x_557_ = v___x_546_;
v_isShared_558_ = v_isSharedCheck_582_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_snapshotTasks_555_);
lean_inc(v_infoState_554_);
lean_inc(v_messages_553_);
lean_inc(v_recordedDeps_552_);
lean_inc(v_traceState_551_);
lean_inc(v_auxDeclNGen_550_);
lean_inc(v_ngen_549_);
lean_inc(v_nextMacroScope_548_);
lean_inc(v_env_547_);
lean_dec(v___x_546_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_582_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
lean_inc(v_currNamespace_545_);
v___x_559_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_547_, v_ext_537_, v_b_538_, v_kind_539_, v_currNamespace_545_);
v___x_560_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 5, v___x_560_);
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_nextMacroScope_548_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_ngen_549_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_auxDeclNGen_550_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_traceState_551_);
lean_ctor_set(v_reuseFailAlloc_581_, 5, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_581_, 6, v_recordedDeps_552_);
lean_ctor_set(v_reuseFailAlloc_581_, 7, v_messages_553_);
lean_ctor_set(v_reuseFailAlloc_581_, 8, v_infoState_554_);
lean_ctor_set(v_reuseFailAlloc_581_, 9, v_snapshotTasks_555_);
v___x_562_ = v_reuseFailAlloc_581_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_mctx_565_; lean_object* v_zetaDeltaFVarIds_566_; lean_object* v_postponed_567_; lean_object* v_diag_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_579_; 
v___x_563_ = lean_st_ref_put(v___y_542_, v___x_562_);
v___x_564_ = lean_st_ref_take(v___y_540_);
v_mctx_565_ = lean_ctor_get(v___x_564_, 0);
v_zetaDeltaFVarIds_566_ = lean_ctor_get(v___x_564_, 2);
v_postponed_567_ = lean_ctor_get(v___x_564_, 3);
v_diag_568_ = lean_ctor_get(v___x_564_, 4);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_564_, 1);
lean_dec(v_unused_580_);
v___x_570_ = v___x_564_;
v_isShared_571_ = v_isSharedCheck_579_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_diag_568_);
lean_inc(v_postponed_567_);
lean_inc(v_zetaDeltaFVarIds_566_);
lean_inc(v_mctx_565_);
lean_dec(v___x_564_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_579_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_572_ = lean_box(0);
v___x_573_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___x_573_);
v___x_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_mctx_565_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_zetaDeltaFVarIds_566_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_postponed_567_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_diag_568_);
v___x_575_ = v_reuseFailAlloc_578_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_st_ref_put(v___y_540_, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_572_);
return v___x_577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___boxed(lean_object* v_ext_584_, lean_object* v_b_585_, lean_object* v_kind_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v_kind_boxed_591_; lean_object* v_res_592_; 
v_kind_boxed_591_ = lean_unbox(v_kind_586_);
v_res_592_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v_ext_584_, v_b_585_, v_kind_boxed_591_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(uint8_t v_attrKind_593_, uint8_t v_post_594_, lean_object* v_as_595_, size_t v_sz_596_, size_t v_i_597_, lean_object* v_b_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_a_605_; uint8_t v___x_609_; 
v___x_609_ = lean_usize_dec_lt(v_i_597_, v_sz_596_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v_b_598_);
return v___x_610_;
}
else
{
lean_object* v___x_611_; lean_object* v_a_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_611_ = lean_box(0);
v_a_612_ = lean_array_uget_borrowed(v_as_595_, v_i_597_);
v___x_613_ = l_Lean_Meta_Grind_normExt;
lean_inc(v_a_612_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v_a_612_);
v___x_615_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_613_, v___x_614_, v_attrKind_593_, v___y_600_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_657_; 
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_615_, 0);
lean_dec(v_unused_658_);
v___x_617_ = v___x_615_;
v_isShared_618_ = v_isSharedCheck_657_;
goto v_resetjp_616_;
}
else
{
lean_dec(v___x_615_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_657_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; 
lean_inc(v_a_612_);
v___x_619_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(v_a_612_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 1);
if (lean_obj_tag(v_a_620_) == 1)
{
lean_object* v_val_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_648_; 
v_val_621_ = lean_ctor_get(v_a_620_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_a_620_);
if (v_isSharedCheck_648_ == 0)
{
v___x_623_ = v_a_620_;
v_isShared_624_ = v_isSharedCheck_648_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_val_621_);
lean_dec(v_a_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_648_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___y_627_; 
v___x_625_ = l_Lean_Meta_Grind_normSymExt;
if (v_post_594_ == 0)
{
lean_object* v___x_643_; 
lean_inc(v_val_621_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_val_621_);
v___x_643_ = v___x_617_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_val_621_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v___y_627_ = v___x_643_;
goto v___jp_626_;
}
}
else
{
lean_object* v___x_646_; 
lean_inc(v_val_621_);
if (v_isShared_618_ == 0)
{
lean_ctor_set_tag(v___x_617_, 1);
lean_ctor_set(v___x_617_, 0, v_val_621_);
v___x_646_ = v___x_617_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_val_621_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
v___y_627_ = v___x_646_;
goto v___jp_626_;
}
}
v___jp_626_:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_625_, v___y_627_, v_attrKind_593_, v___y_600_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_640_; 
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v___x_628_, 0);
lean_dec(v_unused_641_);
v___x_630_ = v___x_628_;
v_isShared_631_ = v_isSharedCheck_640_;
goto v_resetjp_629_;
}
else
{
lean_dec(v___x_628_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_640_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
if (v_post_594_ == 0)
{
lean_del_object(v___x_630_);
lean_del_object(v___x_623_);
lean_dec(v_val_621_);
v_a_605_ = v___x_611_;
goto v___jp_604_;
}
else
{
uint8_t v_rfl_632_; 
v_rfl_632_ = lean_ctor_get_uint8(v_a_612_, sizeof(void*)*5 + 2);
if (v_rfl_632_ == 0)
{
lean_del_object(v___x_630_);
lean_del_object(v___x_623_);
lean_dec(v_val_621_);
v_a_605_ = v___x_611_;
goto v___jp_604_;
}
else
{
lean_object* v___x_634_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v_val_621_);
v___x_634_ = v___x_630_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_val_621_);
v___x_634_ = v_reuseFailAlloc_639_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set_tag(v___x_623_, 2);
lean_ctor_set(v___x_623_, 0, v___x_634_);
v___x_636_ = v___x_623_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_638_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_625_, v___x_636_, v_attrKind_593_, v___y_600_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_dec_ref_known(v___x_637_, 1);
v_a_605_ = v___x_611_;
goto v___jp_604_;
}
else
{
return v___x_637_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_623_);
lean_dec(v_val_621_);
return v___x_628_;
}
}
}
}
else
{
lean_dec(v_a_620_);
lean_del_object(v___x_617_);
v_a_605_ = v___x_611_;
goto v___jp_604_;
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_del_object(v___x_617_);
v_a_649_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_619_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_619_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
else
{
return v___x_615_;
}
}
v___jp_604_:
{
size_t v___x_606_; size_t v___x_607_; 
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_add(v_i_597_, v___x_606_);
v_i_597_ = v___x_607_;
v_b_598_ = v_a_605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2___boxed(lean_object* v_attrKind_659_, lean_object* v_post_660_, lean_object* v_as_661_, lean_object* v_sz_662_, lean_object* v_i_663_, lean_object* v_b_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
uint8_t v_attrKind_boxed_670_; uint8_t v_post_boxed_671_; size_t v_sz_boxed_672_; size_t v_i_boxed_673_; lean_object* v_res_674_; 
v_attrKind_boxed_670_ = lean_unbox(v_attrKind_659_);
v_post_boxed_671_ = lean_unbox(v_post_660_);
v_sz_boxed_672_ = lean_unbox_usize(v_sz_662_);
lean_dec(v_sz_662_);
v_i_boxed_673_ = lean_unbox_usize(v_i_663_);
lean_dec(v_i_663_);
v_res_674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(v_attrKind_boxed_670_, v_post_boxed_671_, v_as_661_, v_sz_boxed_672_, v_i_boxed_673_, v_b_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v_as_661_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(lean_object* v___y_675_, uint8_t v_isExporting_676_, lean_object* v___x_677_, lean_object* v___y_678_, lean_object* v___x_679_, lean_object* v_a_x3f_680_){
_start:
{
lean_object* v___x_682_; lean_object* v_env_683_; lean_object* v_nextMacroScope_684_; lean_object* v_ngen_685_; lean_object* v_auxDeclNGen_686_; lean_object* v_traceState_687_; lean_object* v_recordedDeps_688_; lean_object* v_messages_689_; lean_object* v_infoState_690_; lean_object* v_snapshotTasks_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_716_; 
v___x_682_ = lean_st_ref_take(v___y_675_);
v_env_683_ = lean_ctor_get(v___x_682_, 0);
v_nextMacroScope_684_ = lean_ctor_get(v___x_682_, 1);
v_ngen_685_ = lean_ctor_get(v___x_682_, 2);
v_auxDeclNGen_686_ = lean_ctor_get(v___x_682_, 3);
v_traceState_687_ = lean_ctor_get(v___x_682_, 4);
v_recordedDeps_688_ = lean_ctor_get(v___x_682_, 6);
v_messages_689_ = lean_ctor_get(v___x_682_, 7);
v_infoState_690_ = lean_ctor_get(v___x_682_, 8);
v_snapshotTasks_691_ = lean_ctor_get(v___x_682_, 9);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v___x_682_, 5);
lean_dec(v_unused_717_);
v___x_693_ = v___x_682_;
v_isShared_694_ = v_isSharedCheck_716_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_snapshotTasks_691_);
lean_inc(v_infoState_690_);
lean_inc(v_messages_689_);
lean_inc(v_recordedDeps_688_);
lean_inc(v_traceState_687_);
lean_inc(v_auxDeclNGen_686_);
lean_inc(v_ngen_685_);
lean_inc(v_nextMacroScope_684_);
lean_inc(v_env_683_);
lean_dec(v___x_682_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_716_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = l_Lean_Environment_setExporting(v_env_683_, v_isExporting_676_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 5, v___x_677_);
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_nextMacroScope_684_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_ngen_685_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_auxDeclNGen_686_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_traceState_687_);
lean_ctor_set(v_reuseFailAlloc_715_, 5, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_715_, 6, v_recordedDeps_688_);
lean_ctor_set(v_reuseFailAlloc_715_, 7, v_messages_689_);
lean_ctor_set(v_reuseFailAlloc_715_, 8, v_infoState_690_);
lean_ctor_set(v_reuseFailAlloc_715_, 9, v_snapshotTasks_691_);
v___x_697_ = v_reuseFailAlloc_715_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_mctx_700_; lean_object* v_zetaDeltaFVarIds_701_; lean_object* v_postponed_702_; lean_object* v_diag_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_713_; 
v___x_698_ = lean_st_ref_put(v___y_675_, v___x_697_);
v___x_699_ = lean_st_ref_take(v___y_678_);
v_mctx_700_ = lean_ctor_get(v___x_699_, 0);
v_zetaDeltaFVarIds_701_ = lean_ctor_get(v___x_699_, 2);
v_postponed_702_ = lean_ctor_get(v___x_699_, 3);
v_diag_703_ = lean_ctor_get(v___x_699_, 4);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; 
v_unused_714_ = lean_ctor_get(v___x_699_, 1);
lean_dec(v_unused_714_);
v___x_705_ = v___x_699_;
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_diag_703_);
lean_inc(v_postponed_702_);
lean_inc(v_zetaDeltaFVarIds_701_);
lean_inc(v_mctx_700_);
lean_dec(v___x_699_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_box(0);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v___x_679_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_mctx_700_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_zetaDeltaFVarIds_701_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_postponed_702_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v_diag_703_);
v___x_709_ = v_reuseFailAlloc_712_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_st_ref_put(v___y_678_, v___x_709_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_707_);
return v___x_711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0___boxed(lean_object* v___y_718_, lean_object* v_isExporting_719_, lean_object* v___x_720_, lean_object* v___y_721_, lean_object* v___x_722_, lean_object* v_a_x3f_723_, lean_object* v___y_724_){
_start:
{
uint8_t v_isExporting_boxed_725_; lean_object* v_res_726_; 
v_isExporting_boxed_725_ = lean_unbox(v_isExporting_719_);
v_res_726_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_718_, v_isExporting_boxed_725_, v___x_720_, v___y_721_, v___x_722_, v_a_x3f_723_);
lean_dec(v_a_x3f_723_);
lean_dec(v___y_721_);
lean_dec(v___y_718_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(lean_object* v_x_727_, uint8_t v_isExporting_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; lean_object* v_env_735_; lean_object* v___x_736_; uint8_t v_isModule_737_; 
v___x_734_ = lean_st_ref_get(v___y_732_);
v_env_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_env_735_);
lean_dec(v___x_734_);
v___x_736_ = l_Lean_Environment_header(v_env_735_);
v_isModule_737_ = lean_ctor_get_uint8(v___x_736_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_736_);
if (v_isModule_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec_ref(v_env_735_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
v___x_738_ = lean_apply_5(v_x_727_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, lean_box(0));
return v___x_738_;
}
else
{
uint8_t v_isExporting_739_; 
v_isExporting_739_ = lean_ctor_get_uint8(v_env_735_, sizeof(void*)*13);
lean_dec_ref(v_env_735_);
if (v_isExporting_728_ == 0)
{
if (v_isExporting_739_ == 0)
{
lean_object* v___x_806_; 
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
v___x_806_ = lean_apply_5(v_x_727_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, lean_box(0));
return v___x_806_;
}
else
{
goto v___jp_740_;
}
}
else
{
if (v_isExporting_739_ == 0)
{
goto v___jp_740_;
}
else
{
lean_object* v___x_807_; 
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
v___x_807_ = lean_apply_5(v_x_727_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, lean_box(0));
return v___x_807_;
}
}
v___jp_740_:
{
lean_object* v___x_741_; lean_object* v_env_742_; lean_object* v_nextMacroScope_743_; lean_object* v_ngen_744_; lean_object* v_auxDeclNGen_745_; lean_object* v_traceState_746_; lean_object* v_recordedDeps_747_; lean_object* v_messages_748_; lean_object* v_infoState_749_; lean_object* v_snapshotTasks_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_804_; 
v___x_741_ = lean_st_ref_take(v___y_732_);
v_env_742_ = lean_ctor_get(v___x_741_, 0);
v_nextMacroScope_743_ = lean_ctor_get(v___x_741_, 1);
v_ngen_744_ = lean_ctor_get(v___x_741_, 2);
v_auxDeclNGen_745_ = lean_ctor_get(v___x_741_, 3);
v_traceState_746_ = lean_ctor_get(v___x_741_, 4);
v_recordedDeps_747_ = lean_ctor_get(v___x_741_, 6);
v_messages_748_ = lean_ctor_get(v___x_741_, 7);
v_infoState_749_ = lean_ctor_get(v___x_741_, 8);
v_snapshotTasks_750_ = lean_ctor_get(v___x_741_, 9);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v___x_741_, 5);
lean_dec(v_unused_805_);
v___x_752_ = v___x_741_;
v_isShared_753_ = v_isSharedCheck_804_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snapshotTasks_750_);
lean_inc(v_infoState_749_);
lean_inc(v_messages_748_);
lean_inc(v_recordedDeps_747_);
lean_inc(v_traceState_746_);
lean_inc(v_auxDeclNGen_745_);
lean_inc(v_ngen_744_);
lean_inc(v_nextMacroScope_743_);
lean_inc(v_env_742_);
lean_dec(v___x_741_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_804_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_754_ = l_Lean_Environment_setExporting(v_env_742_, v_isExporting_728_);
v___x_755_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 5, v___x_755_);
lean_ctor_set(v___x_752_, 0, v___x_754_);
v___x_757_ = v___x_752_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_nextMacroScope_743_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_ngen_744_);
lean_ctor_set(v_reuseFailAlloc_803_, 3, v_auxDeclNGen_745_);
lean_ctor_set(v_reuseFailAlloc_803_, 4, v_traceState_746_);
lean_ctor_set(v_reuseFailAlloc_803_, 5, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_803_, 6, v_recordedDeps_747_);
lean_ctor_set(v_reuseFailAlloc_803_, 7, v_messages_748_);
lean_ctor_set(v_reuseFailAlloc_803_, 8, v_infoState_749_);
lean_ctor_set(v_reuseFailAlloc_803_, 9, v_snapshotTasks_750_);
v___x_757_ = v_reuseFailAlloc_803_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_mctx_760_; lean_object* v_zetaDeltaFVarIds_761_; lean_object* v_postponed_762_; lean_object* v_diag_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_801_; 
v___x_758_ = lean_st_ref_put(v___y_732_, v___x_757_);
v___x_759_ = lean_st_ref_take(v___y_730_);
v_mctx_760_ = lean_ctor_get(v___x_759_, 0);
v_zetaDeltaFVarIds_761_ = lean_ctor_get(v___x_759_, 2);
v_postponed_762_ = lean_ctor_get(v___x_759_, 3);
v_diag_763_ = lean_ctor_get(v___x_759_, 4);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v___x_759_, 1);
lean_dec(v_unused_802_);
v___x_765_ = v___x_759_;
v_isShared_766_ = v_isSharedCheck_801_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_diag_763_);
lean_inc(v_postponed_762_);
lean_inc(v_zetaDeltaFVarIds_761_);
lean_inc(v_mctx_760_);
lean_dec(v___x_759_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_801_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_mctx_760_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_zetaDeltaFVarIds_761_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_postponed_762_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v_diag_763_);
v___x_769_ = v_reuseFailAlloc_800_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v_r_771_; 
v___x_770_ = lean_st_ref_put(v___y_730_, v___x_769_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
v_r_771_ = lean_apply_5(v_x_727_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, lean_box(0));
if (lean_obj_tag(v_r_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_788_; 
v_a_772_ = lean_ctor_get(v_r_771_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_r_771_);
if (v_isSharedCheck_788_ == 0)
{
v___x_774_ = v_r_771_;
v_isShared_775_ = v_isSharedCheck_788_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v_r_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_788_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
lean_inc(v_a_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 1);
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_787_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v___x_778_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_732_, v_isExporting_739_, v___x_755_, v___y_730_, v___x_767_, v___x_777_);
lean_dec_ref(v___x_777_);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v___x_778_, 0);
lean_dec(v_unused_786_);
v___x_780_ = v___x_778_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_dec(v___x_778_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v_a_772_);
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_772_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_789_ = lean_ctor_get(v_r_771_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v_r_771_, 1);
v___x_790_ = lean_box(0);
v___x_791_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_732_, v_isExporting_739_, v___x_755_, v___y_730_, v___x_767_, v___x_790_);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v___x_791_, 0);
lean_dec(v_unused_799_);
v___x_793_ = v___x_791_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_dec(v___x_791_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 1);
lean_ctor_set(v___x_793_, 0, v_a_789_);
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_789_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___boxed(lean_object* v_x_808_, lean_object* v_isExporting_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v_isExporting_boxed_815_; lean_object* v_res_816_; 
v_isExporting_boxed_815_ = lean_unbox(v_isExporting_809_);
v_res_816_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_808_, v_isExporting_boxed_815_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object* v_declName_817_, uint8_t v_post_818_, uint8_t v_inv_819_, uint8_t v_attrKind_820_, lean_object* v_prio_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___y_833_; uint8_t v___x_856_; uint8_t v___x_857_; 
v___x_827_ = 1;
v___x_828_ = lean_box(v_post_818_);
v___x_829_ = lean_box(v_inv_819_);
v___x_830_ = lean_box(v___x_827_);
lean_inc(v_declName_817_);
v___x_831_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpTheoremFromConst___boxed), 10, 5);
lean_closure_set(v___x_831_, 0, v_declName_817_);
lean_closure_set(v___x_831_, 1, v___x_828_);
lean_closure_set(v___x_831_, 2, v___x_829_);
lean_closure_set(v___x_831_, 3, v_prio_821_);
lean_closure_set(v___x_831_, 4, v___x_830_);
v___x_856_ = 1;
v___x_857_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_820_, v___x_856_);
if (v___x_857_ == 0)
{
uint8_t v___x_858_; 
v___x_858_ = l_Lean_isPrivateName(v_declName_817_);
lean_dec(v_declName_817_);
if (v___x_858_ == 0)
{
v___y_833_ = v___x_827_;
goto v___jp_832_;
}
else
{
v___y_833_ = v___x_857_;
goto v___jp_832_;
}
}
else
{
uint8_t v___x_859_; 
lean_dec(v_declName_817_);
v___x_859_ = 0;
v___y_833_ = v___x_859_;
goto v___jp_832_;
}
v___jp_832_:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v___x_831_, v___y_833_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_836_; size_t v_sz_837_; size_t v___x_838_; lean_object* v___x_839_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
v___x_836_ = lean_box(0);
v_sz_837_ = lean_array_size(v_a_835_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(v_attrKind_820_, v_post_818_, v_a_835_, v_sz_837_, v___x_838_, v___x_836_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec(v_a_835_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v___x_839_, 0);
lean_dec(v_unused_847_);
v___x_841_ = v___x_839_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_dec(v___x_839_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_836_);
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_836_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
else
{
return v___x_839_;
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_834_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_834_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem___boxed(lean_object* v_declName_860_, lean_object* v_post_861_, lean_object* v_inv_862_, lean_object* v_attrKind_863_, lean_object* v_prio_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
uint8_t v_post_boxed_870_; uint8_t v_inv_boxed_871_; uint8_t v_attrKind_boxed_872_; lean_object* v_res_873_; 
v_post_boxed_870_ = lean_unbox(v_post_861_);
v_inv_boxed_871_ = lean_unbox(v_inv_862_);
v_attrKind_boxed_872_ = lean_unbox(v_attrKind_863_);
v_res_873_ = l_Lean_Meta_Grind_addNormTheorem(v_declName_860_, v_post_boxed_870_, v_inv_boxed_871_, v_attrKind_boxed_872_, v_prio_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(lean_object* v_00_u03b1_874_, lean_object* v_x_875_, uint8_t v_isExporting_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_875_, v_isExporting_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___boxed(lean_object* v_00_u03b1_883_, lean_object* v_x_884_, lean_object* v_isExporting_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v_isExporting_boxed_891_; lean_object* v_res_892_; 
v_isExporting_boxed_891_ = lean_unbox(v_isExporting_885_);
v_res_892_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(v_00_u03b1_883_, v_x_884_, v_isExporting_boxed_891_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(lean_object* v_00_u03b1_893_, lean_object* v_00_u03b2_894_, lean_object* v_00_u03c3_895_, lean_object* v_ext_896_, lean_object* v_b_897_, uint8_t v_kind_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v_ext_896_, v_b_897_, v_kind_898_, v___y_900_, v___y_901_, v___y_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___boxed(lean_object* v_00_u03b1_905_, lean_object* v_00_u03b2_906_, lean_object* v_00_u03c3_907_, lean_object* v_ext_908_, lean_object* v_b_909_, lean_object* v_kind_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v_kind_boxed_916_; lean_object* v_res_917_; 
v_kind_boxed_916_ = lean_unbox(v_kind_910_);
v_res_917_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(v_00_u03b1_905_, v_00_u03b2_906_, v_00_u03c3_907_, v_ext_908_, v_b_909_, v_kind_boxed_916_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg();
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0(lean_object* v_00_u03b2_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(uint8_t v_attrKind_926_, lean_object* v_as_927_, size_t v_sz_928_, size_t v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
uint8_t v___x_935_; 
v___x_935_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v_b_930_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v_a_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_937_ = lean_box(0);
v_a_938_ = lean_array_uget_borrowed(v_as_927_, v_i_929_);
v___x_939_ = l_Lean_Meta_Grind_normSymExt;
lean_inc(v_a_938_);
v___x_940_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_940_, 0, v_a_938_);
v___x_941_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_939_, v___x_940_, v_attrKind_926_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_941_) == 0)
{
size_t v___x_942_; size_t v___x_943_; 
lean_dec_ref_known(v___x_941_, 1);
v___x_942_ = ((size_t)1ULL);
v___x_943_ = lean_usize_add(v_i_929_, v___x_942_);
v_i_929_ = v___x_943_;
v_b_930_ = v___x_937_;
goto _start;
}
else
{
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg___boxed(lean_object* v_attrKind_945_, lean_object* v_as_946_, lean_object* v_sz_947_, lean_object* v_i_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
uint8_t v_attrKind_boxed_954_; size_t v_sz_boxed_955_; size_t v_i_boxed_956_; lean_object* v_res_957_; 
v_attrKind_boxed_954_ = lean_unbox(v_attrKind_945_);
v_sz_boxed_955_ = lean_unbox_usize(v_sz_947_);
lean_dec(v_sz_947_);
v_i_boxed_956_ = lean_unbox_usize(v_i_948_);
lean_dec(v_i_948_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_boxed_954_, v_as_946_, v_sz_boxed_955_, v_i_boxed_956_, v_b_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v_as_946_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(lean_object* v_declName_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; lean_object* v_env_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_961_ = lean_st_ref_get(v___y_959_);
v_env_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc_ref(v_env_962_);
lean_dec(v___x_961_);
v___x_963_ = l_Lean_getReducibilityStatusCore(v_env_962_, v_declName_958_);
v___x_964_ = lean_box(v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg___boxed(lean_object* v_declName_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_966_, v___y_967_);
lean_dec(v___y_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(lean_object* v_declName_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_992_; 
v___x_976_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_970_, v___y_974_);
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_992_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_992_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_992_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
uint8_t v___x_981_; 
v___x_981_ = lean_unbox(v_a_977_);
lean_dec(v_a_977_);
if (v___x_981_ == 0)
{
uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_982_ = 1;
v___x_983_ = lean_box(v___x_982_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_983_);
v___x_985_ = v___x_979_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
else
{
uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_987_ = 0;
v___x_988_ = lean_box(v___x_987_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_988_);
v___x_990_ = v___x_979_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0___boxed(lean_object* v_declName_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(v_declName_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(uint8_t v_attrKind_1000_, lean_object* v_as_1001_, size_t v_sz_1002_, size_t v_i_1003_, lean_object* v_b_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_usize_dec_lt(v_i_1003_, v_sz_1002_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_b_1004_);
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1011_ = lean_box(0);
v_a_1012_ = lean_array_uget_borrowed(v_as_1001_, v_i_1003_);
v___x_1013_ = l_Lean_Meta_Grind_normSymExt;
lean_inc(v_a_1012_);
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_a_1012_);
v___x_1015_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_1013_, v___x_1014_, v_attrKind_1000_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1015_) == 0)
{
size_t v___x_1016_; size_t v___x_1017_; 
lean_dec_ref_known(v___x_1015_, 1);
v___x_1016_ = ((size_t)1ULL);
v___x_1017_ = lean_usize_add(v_i_1003_, v___x_1016_);
v_i_1003_ = v___x_1017_;
v_b_1004_ = v___x_1011_;
goto _start;
}
else
{
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg___boxed(lean_object* v_attrKind_1019_, lean_object* v_as_1020_, lean_object* v_sz_1021_, lean_object* v_i_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
uint8_t v_attrKind_boxed_1028_; size_t v_sz_boxed_1029_; size_t v_i_boxed_1030_; lean_object* v_res_1031_; 
v_attrKind_boxed_1028_ = lean_unbox(v_attrKind_1019_);
v_sz_boxed_1029_ = lean_unbox_usize(v_sz_1021_);
lean_dec(v_sz_1021_);
v_i_boxed_1030_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_res_1031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_boxed_1028_, v_as_1020_, v_sz_boxed_1029_, v_i_boxed_1030_, v_b_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v_as_1020_);
return v_res_1031_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0));
v___x_1034_ = l_Lean_stringToMessageData(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold(lean_object* v_declName_1035_, uint8_t v_attrKind_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1045_; 
lean_inc(v_declName_1035_);
v___x_1045_ = l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(v_declName_1035_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1112_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1112_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1112_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___y_1051_; lean_object* v_a_1052_; uint8_t v___x_1071_; 
v___x_1071_ = lean_unbox(v_a_1046_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_del_object(v___x_1048_);
lean_inc(v_declName_1035_);
v___x_1072_ = l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(v_declName_1035_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; size_t v_sz_1075_; size_t v___x_1076_; lean_object* v___x_1077_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = lean_box(0);
v_sz_1075_ = lean_array_size(v_a_1073_);
v___x_1076_ = ((size_t)0ULL);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_1036_, v_a_1073_, v_sz_1075_, v___x_1076_, v___x_1074_, v_a_1038_, v_a_1039_, v_a_1040_);
lean_dec(v_a_1073_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v___x_1078_; 
lean_dec_ref_known(v___x_1077_, 1);
lean_inc(v_declName_1035_);
v___x_1078_ = l_Lean_Meta_Sym_DSimp_Decls_mkEntries(v_declName_1035_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; size_t v_sz_1080_; lean_object* v___x_1081_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v_sz_1080_ = lean_array_size(v_a_1079_);
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_1036_, v_a_1079_, v_sz_1080_, v___x_1076_, v___x_1074_, v_a_1038_, v_a_1039_, v_a_1040_);
lean_dec(v_a_1079_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1046_);
lean_dec(v_declName_1035_);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v___x_1081_, 0);
lean_dec(v_unused_1089_);
v___x_1083_ = v___x_1081_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_dec(v___x_1081_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1074_);
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1074_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
else
{
lean_object* v_a_1090_; 
v_a_1090_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1090_);
v___y_1051_ = v___x_1081_;
v_a_1052_ = v_a_1090_;
goto v___jp_1050_;
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_a_1091_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1078_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1078_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
lean_inc(v_a_1091_);
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
v___y_1051_ = v___x_1096_;
v_a_1052_ = v_a_1091_;
goto v___jp_1050_;
}
}
}
}
else
{
lean_object* v_a_1099_; 
v_a_1099_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1099_);
v___y_1051_ = v___x_1077_;
v_a_1052_ = v_a_1099_;
goto v___jp_1050_;
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1072_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1072_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
lean_inc(v_a_1100_);
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
v___y_1051_ = v___x_1105_;
v_a_1052_ = v_a_1100_;
goto v___jp_1050_;
}
}
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_dec(v_a_1046_);
lean_dec(v_declName_1035_);
v___x_1108_ = lean_box(0);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1108_);
v___x_1110_ = v___x_1048_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
v___jp_1050_:
{
uint8_t v___x_1053_; 
v___x_1053_ = l_Lean_Exception_isInterrupt(v_a_1052_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; 
lean_inc_ref(v_a_1052_);
v___x_1054_ = l_Lean_Exception_isRuntime(v_a_1052_);
if (v___x_1054_ == 0)
{
lean_object* v_toCold_1055_; lean_object* v_options_1056_; uint8_t v_hasTrace_1057_; 
lean_dec_ref(v___y_1051_);
v_toCold_1055_ = lean_ctor_get(v_a_1039_, 0);
v_options_1056_ = lean_ctor_get(v_toCold_1055_, 2);
v_hasTrace_1057_ = lean_ctor_get_uint8(v_options_1056_, sizeof(void*)*1);
if (v_hasTrace_1057_ == 0)
{
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1046_);
lean_dec(v_declName_1035_);
goto v___jp_1042_;
}
else
{
lean_object* v_inheritedTraceOptions_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_inheritedTraceOptions_1058_ = lean_ctor_get(v_toCold_1055_, 11);
v___x_1059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_1060_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_1061_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1058_, v_options_1056_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1046_);
lean_dec(v_declName_1035_);
goto v___jp_1042_;
}
else
{
lean_object* v___x_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1062_ = lean_obj_once(&l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1, &l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1_once, _init_l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1);
v___x_1063_ = lean_unbox(v_a_1046_);
lean_dec(v_a_1046_);
v___x_1064_ = l_Lean_MessageData_ofConstName(v_declName_1035_, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1062_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = l_Lean_Exception_toMessageData(v_a_1052_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v___x_1059_, v___x_1069_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
return v___x_1070_;
}
}
}
else
{
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1046_);
lean_dec(v_declName_1035_);
return v___y_1051_;
}
}
else
{
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1046_);
lean_dec(v_declName_1035_);
return v___y_1051_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_declName_1035_);
v_a_1113_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1045_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1045_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
v___jp_1042_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___boxed(lean_object* v_declName_1121_, lean_object* v_attrKind_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
uint8_t v_attrKind_boxed_1128_; lean_object* v_res_1129_; 
v_attrKind_boxed_1128_ = lean_unbox(v_attrKind_1122_);
v_res_1129_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v_declName_1121_, v_attrKind_boxed_1128_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(lean_object* v_declName_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_1130_, v___y_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___boxed(lean_object* v_declName_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(v_declName_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(uint8_t v_attrKind_1144_, lean_object* v_as_1145_, size_t v_sz_1146_, size_t v_i_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_1144_, v_as_1145_, v_sz_1146_, v_i_1147_, v_b_1148_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___boxed(lean_object* v_attrKind_1155_, lean_object* v_as_1156_, lean_object* v_sz_1157_, lean_object* v_i_1158_, lean_object* v_b_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v_attrKind_boxed_1165_; size_t v_sz_boxed_1166_; size_t v_i_boxed_1167_; lean_object* v_res_1168_; 
v_attrKind_boxed_1165_ = lean_unbox(v_attrKind_1155_);
v_sz_boxed_1166_ = lean_unbox_usize(v_sz_1157_);
lean_dec(v_sz_1157_);
v_i_boxed_1167_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(v_attrKind_boxed_1165_, v_as_1156_, v_sz_boxed_1166_, v_i_boxed_1167_, v_b_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec_ref(v_as_1156_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(uint8_t v_attrKind_1169_, lean_object* v_as_1170_, size_t v_sz_1171_, size_t v_i_1172_, lean_object* v_b_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_1169_, v_as_1170_, v_sz_1171_, v_i_1172_, v_b_1173_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___boxed(lean_object* v_attrKind_1180_, lean_object* v_as_1181_, lean_object* v_sz_1182_, lean_object* v_i_1183_, lean_object* v_b_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v_attrKind_boxed_1190_; size_t v_sz_boxed_1191_; size_t v_i_boxed_1192_; lean_object* v_res_1193_; 
v_attrKind_boxed_1190_ = lean_unbox(v_attrKind_1180_);
v_sz_boxed_1191_ = lean_unbox_usize(v_sz_1182_);
lean_dec(v_sz_1182_);
v_i_boxed_1192_ = lean_unbox_usize(v_i_1183_);
lean_dec(v_i_1183_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(v_attrKind_boxed_1190_, v_as_1181_, v_sz_boxed_1191_, v_i_boxed_1192_, v_b_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec_ref(v_as_1181_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold(lean_object* v_declName_1194_, uint8_t v_attrKind_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1201_ = l_Lean_Meta_Grind_normExt;
v___x_1202_ = 0;
v___x_1203_ = lean_unsigned_to_nat(1000u);
lean_inc(v_declName_1194_);
v___x_1204_ = l_Lean_Meta_addDeclToUnfold(v___x_1201_, v_declName_1194_, v___x_1202_, v___x_1202_, v___x_1203_, v_attrKind_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1231_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1231_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1231_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_unbox(v_a_1205_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
lean_dec(v_a_1205_);
lean_dec(v_declName_1194_);
v___x_1210_ = lean_box(v___x_1202_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1210_);
v___x_1212_ = v___x_1207_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
else
{
lean_object* v___x_1214_; 
lean_del_object(v___x_1207_);
v___x_1214_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v_declName_1194_, v_attrKind_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1222_);
v___x_1216_ = v___x_1214_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_dec(v___x_1214_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v_a_1205_);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1205_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_a_1205_);
v_a_1223_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1214_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1214_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_1194_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold___boxed(lean_object* v_declName_1232_, lean_object* v_attrKind_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
uint8_t v_attrKind_boxed_1239_; lean_object* v_res_1240_; 
v_attrKind_boxed_1239_ = lean_unbox(v_attrKind_1233_);
v_res_1240_ = l_Lean_Meta_Grind_addNormDeclToUnfold(v_declName_1232_, v_attrKind_boxed_1239_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object* v_x_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_obj_tag_nat(v_x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object* v_x_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(v_x_1243_);
lean_dec(v_x_1243_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_1245_, lean_object* v_k_1246_){
_start:
{
switch(lean_obj_tag(v_t_1245_))
{
case 0:
{
lean_object* v_k_1247_; lean_object* v___x_1248_; 
v_k_1247_ = lean_ctor_get(v_t_1245_, 0);
lean_inc(v_k_1247_);
lean_dec_ref_known(v_t_1245_, 1);
v___x_1248_ = lean_apply_1(v_k_1246_, v_k_1247_);
return v___x_1248_;
}
case 1:
{
uint8_t v_eager_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v_eager_1249_ = lean_ctor_get_uint8(v_t_1245_, 0);
lean_dec_ref_known(v_t_1245_, 0);
v___x_1250_ = lean_box(v_eager_1249_);
v___x_1251_ = lean_apply_1(v_k_1246_, v___x_1250_);
return v___x_1251_;
}
case 5:
{
lean_object* v_prio_1252_; lean_object* v___x_1253_; 
v_prio_1252_ = lean_ctor_get(v_t_1245_, 0);
lean_inc(v_prio_1252_);
lean_dec_ref_known(v_t_1245_, 1);
v___x_1253_ = lean_apply_1(v_k_1246_, v_prio_1252_);
return v___x_1253_;
}
case 8:
{
uint8_t v_post_1254_; uint8_t v_inv_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_post_1254_ = lean_ctor_get_uint8(v_t_1245_, 0);
v_inv_1255_ = lean_ctor_get_uint8(v_t_1245_, 1);
lean_dec_ref_known(v_t_1245_, 0);
v___x_1256_ = lean_box(v_post_1254_);
v___x_1257_ = lean_box(v_inv_1255_);
v___x_1258_ = lean_apply_2(v_k_1246_, v___x_1256_, v___x_1257_);
return v___x_1258_;
}
case 10:
{
uint8_t v_fallback_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_fallback_1259_ = lean_ctor_get_uint8(v_t_1245_, 0);
lean_dec_ref_known(v_t_1245_, 0);
v___x_1260_ = lean_box(v_fallback_1259_);
v___x_1261_ = lean_apply_1(v_k_1246_, v___x_1260_);
return v___x_1261_;
}
default: 
{
lean_dec(v_t_1245_);
return v_k_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_1262_, lean_object* v_ctorIdx_1263_, lean_object* v_t_1264_, lean_object* v_h_1265_, lean_object* v_k_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1264_, v_k_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_1268_, lean_object* v_ctorIdx_1269_, lean_object* v_t_1270_, lean_object* v_h_1271_, lean_object* v_k_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_1268_, v_ctorIdx_1269_, v_t_1270_, v_h_1271_, v_k_1272_);
lean_dec(v_ctorIdx_1269_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_1274_, lean_object* v_ematch_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1274_, v_ematch_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_1277_, lean_object* v_t_1278_, lean_object* v_h_1279_, lean_object* v_ematch_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1278_, v_ematch_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_1282_, lean_object* v_cases_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1282_, v_cases_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_1285_, lean_object* v_t_1286_, lean_object* v_h_1287_, lean_object* v_cases_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1286_, v_cases_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_1290_, lean_object* v_intro_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1290_, v_intro_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_1293_, lean_object* v_t_1294_, lean_object* v_h_1295_, lean_object* v_intro_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1294_, v_intro_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_1298_, lean_object* v_infer_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1298_, v_infer_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_1301_, lean_object* v_t_1302_, lean_object* v_h_1303_, lean_object* v_infer_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1302_, v_infer_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_1306_, lean_object* v_ext_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1306_, v_ext_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_1309_, lean_object* v_t_1310_, lean_object* v_h_1311_, lean_object* v_ext_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1310_, v_ext_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_1314_, lean_object* v_symbol_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1314_, v_symbol_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_1317_, lean_object* v_t_1318_, lean_object* v_h_1319_, lean_object* v_symbol_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1318_, v_symbol_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_1322_, lean_object* v_inj_1323_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1322_, v_inj_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_1325_, lean_object* v_t_1326_, lean_object* v_h_1327_, lean_object* v_inj_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1326_, v_inj_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_1330_, lean_object* v_funCC_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1330_, v_funCC_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_1333_, lean_object* v_t_1334_, lean_object* v_h_1335_, lean_object* v_funCC_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1334_, v_funCC_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_1338_, lean_object* v_norm_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1338_, v_norm_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_1341_, lean_object* v_t_1342_, lean_object* v_h_1343_, lean_object* v_norm_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1342_, v_norm_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_1346_, lean_object* v_unfold_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1346_, v_unfold_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_1349_, lean_object* v_t_1350_, lean_object* v_h_1351_, lean_object* v_unfold_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1350_, v_unfold_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_1354_, lean_object* v_homo_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1354_, v_homo_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_1357_, lean_object* v_t_1358_, lean_object* v_h_1359_, lean_object* v_homo_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1358_, v_homo_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_1362_, lean_object* v_homoPred_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1362_, v_homoPred_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_1365_, lean_object* v_t_1366_, lean_object* v_h_1367_, lean_object* v_homoPred_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1366_, v_homoPred_1368_);
return v___x_1369_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
lean_ctor_set(v___x_1374_, 2, v___x_1373_);
lean_ctor_set(v___x_1374_, 3, v___x_1373_);
lean_ctor_set(v___x_1374_, 4, v___x_1372_);
lean_ctor_set(v___x_1374_, 5, v___x_1372_);
lean_ctor_set(v___x_1374_, 6, v___x_1372_);
lean_ctor_set(v___x_1374_, 7, v___x_1372_);
lean_ctor_set(v___x_1374_, 8, v___x_1372_);
lean_ctor_set(v___x_1374_, 9, v___x_1372_);
lean_ctor_set(v___x_1374_, 10, v___x_1372_);
return v___x_1374_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_unsigned_to_nat(32u);
v___x_1376_ = lean_mk_empty_array_with_capacity(v___x_1375_);
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1378_ = ((size_t)5ULL);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_unsigned_to_nat(32u);
v___x_1381_ = lean_mk_empty_array_with_capacity(v___x_1380_);
v___x_1382_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_1383_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___x_1381_);
lean_ctor_set(v___x_1383_, 2, v___x_1379_);
lean_ctor_set(v___x_1383_, 3, v___x_1379_);
lean_ctor_set_usize(v___x_1383_, 4, v___x_1378_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1384_ = lean_box(1);
v___x_1385_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_1386_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_1387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v___x_1385_);
lean_ctor_set(v___x_1387_, 2, v___x_1384_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; lean_object* v_toCold_1393_; lean_object* v_env_1394_; lean_object* v_options_1395_; uint8_t v___x_1396_; lean_object* v_env_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1392_ = lean_st_ref_get(v___y_1390_);
v_toCold_1393_ = lean_ctor_get(v___y_1389_, 0);
v_env_1394_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_ref(v_env_1394_);
lean_dec(v___x_1392_);
v_options_1395_ = lean_ctor_get(v_toCold_1393_, 2);
v___x_1396_ = 0;
v_env_1397_ = l_Lean_Environment_setRecordingDeps(v_env_1394_, v___x_1396_);
v___x_1398_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_1399_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_1395_);
v___x_1400_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1400_, 0, v_env_1397_);
lean_ctor_set(v___x_1400_, 1, v___x_1398_);
lean_ctor_set(v___x_1400_, 2, v___x_1399_);
lean_ctor_set(v___x_1400_, 3, v_options_1395_);
v___x_1401_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
lean_ctor_set(v___x_1401_, 1, v_msgData_1388_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_ref_1412_; lean_object* v___x_1413_; lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
v_ref_1412_ = lean_ctor_get(v___y_1409_, 2);
v___x_1413_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_1408_, v___y_1409_, v___y_1410_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
lean_inc(v_ref_1412_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_ref_1412_);
lean_ctor_set(v___x_1418_, 1, v_a_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 1);
lean_ctor_set(v___x_1416_, 0, v___x_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_1428_, lean_object* v_msg_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_toCold_1433_; lean_object* v_currRecDepth_1434_; lean_object* v_ref_1435_; uint16_t v_optionFlags_1436_; uint8_t v_suppressElabErrors_1437_; uint8_t v_checkDeprecated_1438_; uint8_t v_isRecordingDeps_1439_; lean_object* v_ref_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_toCold_1433_ = lean_ctor_get(v___y_1430_, 0);
v_currRecDepth_1434_ = lean_ctor_get(v___y_1430_, 1);
v_ref_1435_ = lean_ctor_get(v___y_1430_, 2);
v_optionFlags_1436_ = lean_ctor_get_uint16(v___y_1430_, sizeof(void*)*3);
v_suppressElabErrors_1437_ = lean_ctor_get_uint8(v___y_1430_, sizeof(void*)*3 + 2);
v_checkDeprecated_1438_ = lean_ctor_get_uint8(v___y_1430_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1439_ = lean_ctor_get_uint8(v___y_1430_, sizeof(void*)*3 + 4);
v_ref_1440_ = l_Lean_replaceRef(v_ref_1428_, v_ref_1435_);
lean_inc(v_currRecDepth_1434_);
lean_inc_ref(v_toCold_1433_);
v___x_1441_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1441_, 0, v_toCold_1433_);
lean_ctor_set(v___x_1441_, 1, v_currRecDepth_1434_);
lean_ctor_set(v___x_1441_, 2, v_ref_1440_);
lean_ctor_set_uint16(v___x_1441_, sizeof(void*)*3, v_optionFlags_1436_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 2, v_suppressElabErrors_1437_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 3, v_checkDeprecated_1438_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 4, v_isRecordingDeps_1439_);
v___x_1442_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1429_, v___x_1441_, v___y_1431_);
lean_dec_ref_known(v___x_1441_, 3);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_1443_, lean_object* v_msg_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_1443_, v_msg_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v_ref_1443_);
return v_res_1448_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
v___x_1458_ = l_Lean_stringToMessageData(v___x_1457_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__5));
v___x_1461_ = l_Lean_stringToMessageData(v___x_1460_);
return v___x_1461_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__54(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__53));
v___x_1602_ = l_Lean_stringToMessageData(v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__2));
lean_inc(v_stx_1629_);
v___x_1634_ = l_Lean_Syntax_isOfKind(v_stx_1629_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1635_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1636_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1639_, v_a_1630_, v_a_1631_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = l_Lean_Syntax_getArg(v_stx_1629_, v___x_1641_);
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__8));
lean_inc(v___x_1642_);
v___x_1644_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__10));
lean_inc(v___x_1642_);
v___x_1646_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__12));
lean_inc(v___x_1642_);
v___x_1648_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__14));
lean_inc(v___x_1642_);
v___x_1650_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__16));
lean_inc(v___x_1642_);
v___x_1652_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__18));
lean_inc(v___x_1642_);
v___x_1654_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__20));
lean_inc(v___x_1642_);
v___x_1656_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__22));
lean_inc(v___x_1642_);
v___x_1658_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__24));
lean_inc(v___x_1642_);
v___x_1660_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__26));
lean_inc(v___x_1642_);
v___x_1662_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
lean_inc(v___x_1642_);
v___x_1664_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__30));
lean_inc(v___x_1642_);
v___x_1666_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1665_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1667_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__32));
lean_inc(v___x_1642_);
v___x_1668_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__34));
lean_inc(v___x_1642_);
v___x_1670_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__36));
lean_inc(v___x_1642_);
v___x_1672_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__38));
lean_inc(v___x_1642_);
v___x_1674_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__40));
lean_inc(v___x_1642_);
v___x_1676_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__42));
lean_inc(v___x_1642_);
v___x_1678_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__44));
lean_inc(v___x_1642_);
v___x_1680_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__46));
lean_inc(v___x_1642_);
v___x_1682_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1683_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__48));
lean_inc(v___x_1642_);
v___x_1684_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__50));
lean_inc(v___x_1642_);
v___x_1686_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__52));
lean_inc(v___x_1642_);
v___x_1688_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec(v___x_1642_);
v___x_1689_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1690_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1693_, v_a_1630_, v_a_1631_);
return v___x_1694_;
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v_stx_1629_);
v___x_1695_ = lean_unsigned_to_nat(1u);
v___x_1696_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1695_);
lean_dec(v___x_1642_);
v___x_1697_ = l_Lean_Syntax_isNatLit_x3f(v___x_1696_);
if (lean_obj_tag(v___x_1697_) == 1)
{
lean_object* v_val_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v___x_1696_);
v_val_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_val_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 5);
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_val_1698_);
v___x_1703_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec(v___x_1697_);
v___x_1707_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__54, &l_Lean_Meta_Grind_getAttrKindCore___closed__54_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__54);
v___x_1708_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_1696_, v___x_1707_, v_a_1630_, v_a_1631_);
lean_dec(v___x_1696_);
return v___x_1708_;
}
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1709_ = lean_box(11);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1711_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_1711_, 0, v___x_1634_);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
return v___x_1712_;
}
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1713_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_1713_, 0, v___x_1680_);
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1715_ = lean_box(9);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1717_ = lean_unsigned_to_nat(1u);
v___x_1718_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1717_);
lean_inc(v___x_1718_);
v___x_1719_ = l_Lean_Syntax_matchesNull(v___x_1718_, v___x_1641_);
if (v___x_1719_ == 0)
{
uint8_t v___x_1720_; 
lean_inc(v___x_1718_);
v___x_1720_ = l_Lean_Syntax_matchesNull(v___x_1718_, v___x_1717_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_dec(v___x_1718_);
lean_dec(v___x_1642_);
v___x_1721_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1722_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1725_, v_a_1630_, v_a_1631_);
return v___x_1726_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = l_Lean_Syntax_getArg(v___x_1718_, v___x_1641_);
lean_dec(v___x_1718_);
v___x_1728_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
lean_inc(v___x_1727_);
v___x_1729_ = l_Lean_Syntax_isOfKind(v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_1731_ = l_Lean_Syntax_isOfKind(v___x_1727_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec(v___x_1642_);
v___x_1732_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1733_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1736_, v_a_1630_, v_a_1631_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1738_ = lean_unsigned_to_nat(2u);
v___x_1739_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1738_);
lean_dec(v___x_1642_);
lean_inc(v___x_1739_);
v___x_1740_ = l_Lean_Syntax_matchesNull(v___x_1739_, v___x_1641_);
if (v___x_1740_ == 0)
{
uint8_t v___x_1741_; 
v___x_1741_ = l_Lean_Syntax_matchesNull(v___x_1739_, v___x_1717_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1742_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1743_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1746_, v_a_1630_, v_a_1631_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v_stx_1629_);
v___x_1748_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1748_, 0, v___x_1740_);
lean_ctor_set_uint8(v___x_1748_, 1, v___x_1634_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v___x_1739_);
lean_dec(v_stx_1629_);
v___x_1750_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1750_, 0, v___x_1729_);
lean_ctor_set_uint8(v___x_1750_, 1, v___x_1729_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
lean_dec(v___x_1727_);
v___x_1752_ = lean_unsigned_to_nat(2u);
v___x_1753_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1752_);
lean_dec(v___x_1642_);
lean_inc(v___x_1753_);
v___x_1754_ = l_Lean_Syntax_matchesNull(v___x_1753_, v___x_1641_);
if (v___x_1754_ == 0)
{
uint8_t v___x_1755_; 
v___x_1755_ = l_Lean_Syntax_matchesNull(v___x_1753_, v___x_1717_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1756_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1757_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1760_, v_a_1630_, v_a_1631_);
return v___x_1761_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v_stx_1629_);
v___x_1762_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1762_, 0, v___x_1634_);
lean_ctor_set_uint8(v___x_1762_, 1, v___x_1634_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v___x_1753_);
lean_dec(v_stx_1629_);
v___x_1764_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1764_, 0, v___x_1634_);
lean_ctor_set_uint8(v___x_1764_, 1, v___x_1719_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
lean_dec(v___x_1718_);
v___x_1766_ = lean_unsigned_to_nat(2u);
v___x_1767_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1766_);
lean_dec(v___x_1642_);
lean_inc(v___x_1767_);
v___x_1768_ = l_Lean_Syntax_matchesNull(v___x_1767_, v___x_1641_);
if (v___x_1768_ == 0)
{
uint8_t v___x_1769_; 
v___x_1769_ = l_Lean_Syntax_matchesNull(v___x_1767_, v___x_1717_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1770_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1771_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1774_, v_a_1630_, v_a_1631_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v_stx_1629_);
v___x_1776_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1776_, 0, v___x_1634_);
lean_ctor_set_uint8(v___x_1776_, 1, v___x_1634_);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v___x_1767_);
lean_dec(v_stx_1629_);
v___x_1778_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1778_, 0, v___x_1634_);
lean_ctor_set_uint8(v___x_1778_, 1, v___x_1676_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
return v___x_1779_;
}
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1780_ = lean_box(7);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1782_ = lean_box(6);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1784_ = lean_box(4);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
return v___x_1785_;
}
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1786_ = lean_box(2);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1788_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1788_, 0, v___x_1634_);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
return v___x_1789_;
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1790_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1790_, 0, v___x_1664_);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1792_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1792_, 0, v___x_1634_);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1795_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1797_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1799_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1801_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1803_ = lean_unsigned_to_nat(3u);
v___x_1804_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1803_);
lean_dec(v___x_1642_);
lean_inc(v___x_1804_);
v___x_1805_ = l_Lean_Syntax_matchesNull(v___x_1804_, v___x_1641_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1804_);
v___x_1807_ = l_Lean_Syntax_matchesNull(v___x_1804_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec(v___x_1804_);
v___x_1808_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1809_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1812_, v_a_1630_, v_a_1631_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1814_ = l_Lean_Syntax_getArg(v___x_1804_, v___x_1641_);
lean_dec(v___x_1804_);
v___x_1815_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1816_ = l_Lean_Syntax_isOfKind(v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1817_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1818_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1821_, v_a_1630_, v_a_1631_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v_stx_1629_);
v___x_1823_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1823_, 0, v___x_1634_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
}
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec(v___x_1804_);
lean_dec(v_stx_1629_);
v___x_1826_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1826_, 0, v___x_1652_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
}
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1829_ = lean_unsigned_to_nat(2u);
v___x_1830_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1829_);
lean_dec(v___x_1642_);
lean_inc(v___x_1830_);
v___x_1831_ = l_Lean_Syntax_matchesNull(v___x_1830_, v___x_1641_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1830_);
v___x_1833_ = l_Lean_Syntax_matchesNull(v___x_1830_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v___x_1830_);
v___x_1834_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1835_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1838_, v_a_1630_, v_a_1631_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = l_Lean_Syntax_getArg(v___x_1830_, v___x_1641_);
lean_dec(v___x_1830_);
v___x_1841_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1842_ = l_Lean_Syntax_isOfKind(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1843_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1844_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1843_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1847_, v_a_1630_, v_a_1631_);
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec(v_stx_1629_);
v___x_1849_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1849_, 0, v___x_1634_);
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_dec(v___x_1830_);
lean_dec(v_stx_1629_);
v___x_1852_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1852_, 0, v___x_1650_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1855_);
lean_dec(v___x_1642_);
lean_inc(v___x_1856_);
v___x_1857_ = l_Lean_Syntax_matchesNull(v___x_1856_, v___x_1641_);
if (v___x_1857_ == 0)
{
uint8_t v___x_1858_; 
lean_inc(v___x_1856_);
v___x_1858_ = l_Lean_Syntax_matchesNull(v___x_1856_, v___x_1855_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec(v___x_1856_);
v___x_1859_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1860_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1863_, v_a_1630_, v_a_1631_);
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1865_ = l_Lean_Syntax_getArg(v___x_1856_, v___x_1641_);
lean_dec(v___x_1856_);
v___x_1866_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1867_ = l_Lean_Syntax_isOfKind(v___x_1865_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1868_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1869_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1872_, v_a_1630_, v_a_1631_);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
lean_dec(v_stx_1629_);
v___x_1874_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_1874_, 0, v___x_1634_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
}
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec(v___x_1856_);
lean_dec(v_stx_1629_);
v___x_1877_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_1877_, 0, v___x_1648_);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_dec(v___x_1642_);
lean_dec(v_stx_1629_);
v___x_1880_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1882_ = lean_unsigned_to_nat(1u);
v___x_1883_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1882_);
lean_dec(v___x_1642_);
lean_inc(v___x_1883_);
v___x_1884_ = l_Lean_Syntax_matchesNull(v___x_1883_, v___x_1641_);
if (v___x_1884_ == 0)
{
uint8_t v___x_1885_; 
lean_inc(v___x_1883_);
v___x_1885_ = l_Lean_Syntax_matchesNull(v___x_1883_, v___x_1882_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec(v___x_1883_);
v___x_1886_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1887_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1890_, v_a_1630_, v_a_1631_);
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1892_ = l_Lean_Syntax_getArg(v___x_1883_, v___x_1641_);
lean_dec(v___x_1883_);
v___x_1893_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1894_ = l_Lean_Syntax_isOfKind(v___x_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1895_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1896_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1899_, v_a_1630_, v_a_1631_);
return v___x_1900_;
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec(v_stx_1629_);
v___x_1901_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1901_, 0, v___x_1634_);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_dec(v___x_1883_);
lean_dec(v_stx_1629_);
v___x_1904_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1904_, 0, v___x_1644_);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
return v___x_1906_;
}
}
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1907_ = lean_unsigned_to_nat(1u);
v___x_1908_ = l_Lean_Syntax_getArg(v___x_1642_, v___x_1907_);
lean_dec(v___x_1642_);
lean_inc(v___x_1908_);
v___x_1909_ = l_Lean_Syntax_matchesNull(v___x_1908_, v___x_1641_);
if (v___x_1909_ == 0)
{
uint8_t v___x_1910_; 
lean_inc(v___x_1908_);
v___x_1910_ = l_Lean_Syntax_matchesNull(v___x_1908_, v___x_1907_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec(v___x_1908_);
v___x_1911_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1912_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1915_, v_a_1630_, v_a_1631_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1917_ = l_Lean_Syntax_getArg(v___x_1908_, v___x_1641_);
lean_dec(v___x_1908_);
v___x_1918_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1919_ = l_Lean_Syntax_isOfKind(v___x_1917_, v___x_1918_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1920_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1921_ = l_Lean_MessageData_ofSyntax(v_stx_1629_);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1924_, v_a_1630_, v_a_1631_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec(v_stx_1629_);
v___x_1926_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1926_, 0, v___x_1634_);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
}
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_dec(v___x_1908_);
lean_dec(v_stx_1629_);
v___x_1929_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_1936_, lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1937_, v___y_1938_, v___y_1939_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_1942_, lean_object* v_msg_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_1942_, v_msg_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_1948_, lean_object* v_ref_1949_, lean_object* v_msg_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_1949_, v_msg_1950_, v___y_1951_, v___y_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_1955_, lean_object* v_ref_1956_, lean_object* v_msg_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_1955_, v_ref_1956_, v_msg_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_ref_1956_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1966_ = lean_unsigned_to_nat(1u);
v___x_1967_ = l_Lean_Syntax_getArg(v_stx_1962_, v___x_1966_);
v___x_1968_ = l_Lean_Syntax_isNone(v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_unsigned_to_nat(0u);
v___x_1970_ = l_Lean_Syntax_getArg(v___x_1967_, v___x_1969_);
lean_dec(v___x_1967_);
v___x_1971_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_1970_, v_a_1963_, v_a_1964_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec(v___x_1967_);
v___x_1972_ = lean_box(3);
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
return v___x_1973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_stx_1974_);
return v_res_1978_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_1981_ = l_Lean_stringToMessageData(v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_1986_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1985_, v_a_1982_, v_a_1983_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_1987_, v_a_1988_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_1992_, v_a_1993_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_1996_, v_a_1997_, v_a_1998_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_2001_, lean_object* v_b_2002_, uint8_t v_kind_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_toCold_2007_; lean_object* v_currNamespace_2008_; lean_object* v___x_2009_; lean_object* v_env_2010_; lean_object* v_nextMacroScope_2011_; lean_object* v_ngen_2012_; lean_object* v_auxDeclNGen_2013_; lean_object* v_traceState_2014_; lean_object* v_recordedDeps_2015_; lean_object* v_messages_2016_; lean_object* v_infoState_2017_; lean_object* v_snapshotTasks_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2030_; 
v_toCold_2007_ = lean_ctor_get(v___y_2004_, 0);
v_currNamespace_2008_ = lean_ctor_get(v_toCold_2007_, 4);
v___x_2009_ = lean_st_ref_take(v___y_2005_);
v_env_2010_ = lean_ctor_get(v___x_2009_, 0);
v_nextMacroScope_2011_ = lean_ctor_get(v___x_2009_, 1);
v_ngen_2012_ = lean_ctor_get(v___x_2009_, 2);
v_auxDeclNGen_2013_ = lean_ctor_get(v___x_2009_, 3);
v_traceState_2014_ = lean_ctor_get(v___x_2009_, 4);
v_recordedDeps_2015_ = lean_ctor_get(v___x_2009_, 6);
v_messages_2016_ = lean_ctor_get(v___x_2009_, 7);
v_infoState_2017_ = lean_ctor_get(v___x_2009_, 8);
v_snapshotTasks_2018_ = lean_ctor_get(v___x_2009_, 9);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v___x_2009_, 5);
lean_dec(v_unused_2031_);
v___x_2020_ = v___x_2009_;
v_isShared_2021_ = v_isSharedCheck_2030_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_snapshotTasks_2018_);
lean_inc(v_infoState_2017_);
lean_inc(v_messages_2016_);
lean_inc(v_recordedDeps_2015_);
lean_inc(v_traceState_2014_);
lean_inc(v_auxDeclNGen_2013_);
lean_inc(v_ngen_2012_);
lean_inc(v_nextMacroScope_2011_);
lean_inc(v_env_2010_);
lean_dec(v___x_2009_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2030_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2022_ = lean_box(0);
lean_inc(v_currNamespace_2008_);
v___x_2023_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2010_, v_ext_2001_, v_b_2002_, v_kind_2003_, v_currNamespace_2008_);
v___x_2024_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 5, v___x_2024_);
lean_ctor_set(v___x_2020_, 0, v___x_2023_);
v___x_2026_ = v___x_2020_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_nextMacroScope_2011_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_ngen_2012_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_auxDeclNGen_2013_);
lean_ctor_set(v_reuseFailAlloc_2029_, 4, v_traceState_2014_);
lean_ctor_set(v_reuseFailAlloc_2029_, 5, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2029_, 6, v_recordedDeps_2015_);
lean_ctor_set(v_reuseFailAlloc_2029_, 7, v_messages_2016_);
lean_ctor_set(v_reuseFailAlloc_2029_, 8, v_infoState_2017_);
lean_ctor_set(v_reuseFailAlloc_2029_, 9, v_snapshotTasks_2018_);
v___x_2026_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_st_ref_put(v___y_2005_, v___x_2026_);
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2022_);
return v___x_2028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_2032_, lean_object* v_b_2033_, lean_object* v_kind_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
uint8_t v_kind_boxed_2038_; lean_object* v_res_2039_; 
v_kind_boxed_2038_ = lean_unbox(v_kind_2034_);
v_res_2039_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2032_, v_b_2033_, v_kind_boxed_2038_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_2040_, lean_object* v_00_u03b2_2041_, lean_object* v_00_u03c3_2042_, lean_object* v_ext_2043_, lean_object* v_b_2044_, uint8_t v_kind_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2043_, v_b_2044_, v_kind_2045_, v___y_2046_, v___y_2047_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_2050_, lean_object* v_00_u03b2_2051_, lean_object* v_00_u03c3_2052_, lean_object* v_ext_2053_, lean_object* v_b_2054_, lean_object* v_kind_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v_kind_boxed_2059_; lean_object* v_res_2060_; 
v_kind_boxed_2059_ = lean_unbox(v_kind_2055_);
v_res_2060_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_2050_, v_00_u03b2_2051_, v_00_u03c3_2052_, v_ext_2053_, v_b_2054_, v_kind_boxed_2059_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_2061_, lean_object* v_declName_2062_, uint8_t v_eager_2063_, uint8_t v_attrKind_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v___x_2068_; 
lean_inc(v_declName_2062_);
v___x_2068_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_2062_, v_eager_2063_, v_a_2065_, v_a_2066_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_dec_ref_known(v___x_2068_, 1);
v___x_2069_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2069_, 0, v_declName_2062_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*1, v_eager_2063_);
v___x_2070_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2061_, v___x_2069_, v_attrKind_2064_, v_a_2065_, v_a_2066_);
return v___x_2070_;
}
else
{
lean_dec(v_declName_2062_);
lean_dec_ref(v_ext_2061_);
return v___x_2068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_2071_, lean_object* v_declName_2072_, lean_object* v_eager_2073_, lean_object* v_attrKind_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
uint8_t v_eager_boxed_2078_; uint8_t v_attrKind_boxed_2079_; lean_object* v_res_2080_; 
v_eager_boxed_2078_ = lean_unbox(v_eager_2073_);
v_attrKind_boxed_2079_ = lean_unbox(v_attrKind_2074_);
v_res_2080_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2071_, v_declName_2072_, v_eager_boxed_2078_, v_attrKind_boxed_2079_, v_a_2075_, v_a_2076_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_2081_, lean_object* v_declName_2082_, uint8_t v_attrKind_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2087_; 
lean_inc(v_declName_2082_);
v___x_2087_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_2082_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2095_; 
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v___x_2087_, 0);
lean_dec(v_unused_2096_);
v___x_2089_ = v___x_2087_;
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
else
{
lean_dec(v___x_2087_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v_declName_2082_);
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_declName_2082_);
v___x_2092_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2081_, v___x_2092_, v_attrKind_2083_, v_a_2084_, v_a_2085_);
return v___x_2093_;
}
}
}
else
{
lean_dec(v_declName_2082_);
lean_dec_ref(v_ext_2081_);
return v___x_2087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_2097_, lean_object* v_declName_2098_, lean_object* v_attrKind_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
uint8_t v_attrKind_boxed_2103_; lean_object* v_res_2104_; 
v_attrKind_boxed_2103_ = lean_unbox(v_attrKind_2099_);
v_res_2104_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2097_, v_declName_2098_, v_attrKind_boxed_2103_, v_a_2100_, v_a_2101_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_2105_, lean_object* v_declName_2106_, uint8_t v_attrKind_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_declName_2106_);
v___x_2112_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2105_, v___x_2111_, v_attrKind_2107_, v_a_2108_, v_a_2109_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_2113_, lean_object* v_declName_2114_, lean_object* v_attrKind_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
uint8_t v_attrKind_boxed_2119_; lean_object* v_res_2120_; 
v_attrKind_boxed_2119_ = lean_unbox(v_attrKind_2115_);
v_res_2120_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2113_, v_declName_2114_, v_attrKind_boxed_2119_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_2121_, lean_object* v_s_2122_){
_start:
{
lean_object* v_casesTypes_2123_; lean_object* v_funCC_2124_; lean_object* v_ematch_2125_; lean_object* v_inj_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
v_casesTypes_2123_ = lean_ctor_get(v_s_2122_, 0);
v_funCC_2124_ = lean_ctor_get(v_s_2122_, 2);
v_ematch_2125_ = lean_ctor_get(v_s_2122_, 3);
v_inj_2126_ = lean_ctor_get(v_s_2122_, 4);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_s_2122_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v_s_2122_, 1);
lean_dec(v_unused_2134_);
v___x_2128_ = v_s_2122_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_inj_2126_);
lean_inc(v_ematch_2125_);
lean_inc(v_funCC_2124_);
lean_inc(v_casesTypes_2123_);
lean_dec(v_s_2122_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_a_2121_);
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_casesTypes_2123_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_a_2121_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_funCC_2124_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_ematch_2125_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v_inj_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_2135_, lean_object* v_declName_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v_ext_2142_; lean_object* v_toEnvExtension_2143_; lean_object* v_env_2144_; lean_object* v_asyncMode_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; lean_object* v_extThms_2148_; lean_object* v___x_2149_; 
v___x_2140_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2141_ = lean_st_ref_get(v_a_2138_);
v_ext_2142_ = lean_ctor_get(v_ext_2135_, 1);
v_toEnvExtension_2143_ = lean_ctor_get(v_ext_2142_, 0);
v_env_2144_ = lean_ctor_get(v___x_2141_, 0);
lean_inc_ref(v_env_2144_);
lean_dec(v___x_2141_);
v_asyncMode_2145_ = lean_ctor_get(v_toEnvExtension_2143_, 2);
v___x_2146_ = 0;
v___x_2147_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2140_, v_ext_2135_, v_env_2144_, v_asyncMode_2145_, v___x_2146_);
v_extThms_2148_ = lean_ctor_get(v___x_2147_, 1);
lean_inc_ref(v_extThms_2148_);
lean_dec(v___x_2147_);
v___x_2149_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_2148_, v_declName_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2180_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2180_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2180_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___f_2154_; lean_object* v___x_2155_; lean_object* v_env_2156_; lean_object* v_nextMacroScope_2157_; lean_object* v_ngen_2158_; lean_object* v_auxDeclNGen_2159_; lean_object* v_traceState_2160_; lean_object* v_recordedDeps_2161_; lean_object* v_messages_2162_; lean_object* v_infoState_2163_; lean_object* v_snapshotTasks_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2178_; 
v___f_2154_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_2154_, 0, v_a_2150_);
v___x_2155_ = lean_st_ref_take(v_a_2138_);
v_env_2156_ = lean_ctor_get(v___x_2155_, 0);
v_nextMacroScope_2157_ = lean_ctor_get(v___x_2155_, 1);
v_ngen_2158_ = lean_ctor_get(v___x_2155_, 2);
v_auxDeclNGen_2159_ = lean_ctor_get(v___x_2155_, 3);
v_traceState_2160_ = lean_ctor_get(v___x_2155_, 4);
v_recordedDeps_2161_ = lean_ctor_get(v___x_2155_, 6);
v_messages_2162_ = lean_ctor_get(v___x_2155_, 7);
v_infoState_2163_ = lean_ctor_get(v___x_2155_, 8);
v_snapshotTasks_2164_ = lean_ctor_get(v___x_2155_, 9);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; 
v_unused_2179_ = lean_ctor_get(v___x_2155_, 5);
lean_dec(v_unused_2179_);
v___x_2166_ = v___x_2155_;
v_isShared_2167_ = v_isSharedCheck_2178_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_snapshotTasks_2164_);
lean_inc(v_infoState_2163_);
lean_inc(v_messages_2162_);
lean_inc(v_recordedDeps_2161_);
lean_inc(v_traceState_2160_);
lean_inc(v_auxDeclNGen_2159_);
lean_inc(v_ngen_2158_);
lean_inc(v_nextMacroScope_2157_);
lean_inc(v_env_2156_);
lean_dec(v___x_2155_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2178_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2168_ = lean_box(0);
v___x_2169_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2135_, v_env_2156_, v___f_2154_);
v___x_2170_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 5, v___x_2170_);
lean_ctor_set(v___x_2166_, 0, v___x_2169_);
v___x_2172_ = v___x_2166_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_nextMacroScope_2157_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_ngen_2158_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_auxDeclNGen_2159_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_traceState_2160_);
lean_ctor_set(v_reuseFailAlloc_2177_, 5, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2177_, 6, v_recordedDeps_2161_);
lean_ctor_set(v_reuseFailAlloc_2177_, 7, v_messages_2162_);
lean_ctor_set(v_reuseFailAlloc_2177_, 8, v_infoState_2163_);
lean_ctor_set(v_reuseFailAlloc_2177_, 9, v_snapshotTasks_2164_);
v___x_2172_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = lean_st_ref_put(v_a_2138_, v___x_2172_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2168_);
v___x_2175_ = v___x_2152_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2168_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v_ext_2135_);
v_a_2181_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2149_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2149_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_2189_, lean_object* v_declName_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2189_, v_declName_2190_, v_a_2191_, v_a_2192_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_2195_, lean_object* v_s_2196_){
_start:
{
lean_object* v_extThms_2197_; lean_object* v_funCC_2198_; lean_object* v_ematch_2199_; lean_object* v_inj_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
v_extThms_2197_ = lean_ctor_get(v_s_2196_, 1);
v_funCC_2198_ = lean_ctor_get(v_s_2196_, 2);
v_ematch_2199_ = lean_ctor_get(v_s_2196_, 3);
v_inj_2200_ = lean_ctor_get(v_s_2196_, 4);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_s_2196_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; 
v_unused_2208_ = lean_ctor_get(v_s_2196_, 0);
lean_dec(v_unused_2208_);
v___x_2202_ = v_s_2196_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_inj_2200_);
lean_inc(v_ematch_2199_);
lean_inc(v_funCC_2198_);
lean_inc(v_extThms_2197_);
lean_dec(v_s_2196_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v_a_2195_);
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2195_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_extThms_2197_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_funCC_2198_);
lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_ematch_2199_);
lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_inj_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_2209_, lean_object* v_declName_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_inc(v_declName_2210_);
v___x_2215_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_2210_, v_a_2211_, v_a_2212_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v___x_2216_; lean_object* v_ext_2217_; lean_object* v_toEnvExtension_2218_; lean_object* v_env_2219_; lean_object* v_asyncMode_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v_casesTypes_2223_; lean_object* v___x_2224_; 
lean_dec_ref_known(v___x_2215_, 1);
v___x_2216_ = lean_st_ref_get(v_a_2212_);
v_ext_2217_ = lean_ctor_get(v_ext_2209_, 1);
v_toEnvExtension_2218_ = lean_ctor_get(v_ext_2217_, 0);
v_env_2219_ = lean_ctor_get(v___x_2216_, 0);
lean_inc_ref(v_env_2219_);
lean_dec(v___x_2216_);
v_asyncMode_2220_ = lean_ctor_get(v_toEnvExtension_2218_, 2);
v___x_2221_ = 0;
v___x_2222_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2214_, v_ext_2209_, v_env_2219_, v_asyncMode_2220_, v___x_2221_);
v_casesTypes_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc_ref(v_casesTypes_2223_);
lean_dec(v___x_2222_);
v___x_2224_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_2223_, v_declName_2210_, v_a_2211_, v_a_2212_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2255_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2255_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2255_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___f_2229_; lean_object* v___x_2230_; lean_object* v_env_2231_; lean_object* v_nextMacroScope_2232_; lean_object* v_ngen_2233_; lean_object* v_auxDeclNGen_2234_; lean_object* v_traceState_2235_; lean_object* v_recordedDeps_2236_; lean_object* v_messages_2237_; lean_object* v_infoState_2238_; lean_object* v_snapshotTasks_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2253_; 
v___f_2229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_2229_, 0, v_a_2225_);
v___x_2230_ = lean_st_ref_take(v_a_2212_);
v_env_2231_ = lean_ctor_get(v___x_2230_, 0);
v_nextMacroScope_2232_ = lean_ctor_get(v___x_2230_, 1);
v_ngen_2233_ = lean_ctor_get(v___x_2230_, 2);
v_auxDeclNGen_2234_ = lean_ctor_get(v___x_2230_, 3);
v_traceState_2235_ = lean_ctor_get(v___x_2230_, 4);
v_recordedDeps_2236_ = lean_ctor_get(v___x_2230_, 6);
v_messages_2237_ = lean_ctor_get(v___x_2230_, 7);
v_infoState_2238_ = lean_ctor_get(v___x_2230_, 8);
v_snapshotTasks_2239_ = lean_ctor_get(v___x_2230_, 9);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v___x_2230_, 5);
lean_dec(v_unused_2254_);
v___x_2241_ = v___x_2230_;
v_isShared_2242_ = v_isSharedCheck_2253_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_snapshotTasks_2239_);
lean_inc(v_infoState_2238_);
lean_inc(v_messages_2237_);
lean_inc(v_recordedDeps_2236_);
lean_inc(v_traceState_2235_);
lean_inc(v_auxDeclNGen_2234_);
lean_inc(v_ngen_2233_);
lean_inc(v_nextMacroScope_2232_);
lean_inc(v_env_2231_);
lean_dec(v___x_2230_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2253_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2243_ = lean_box(0);
v___x_2244_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2209_, v_env_2231_, v___f_2229_);
v___x_2245_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 5, v___x_2245_);
lean_ctor_set(v___x_2241_, 0, v___x_2244_);
v___x_2247_ = v___x_2241_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_nextMacroScope_2232_);
lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_ngen_2233_);
lean_ctor_set(v_reuseFailAlloc_2252_, 3, v_auxDeclNGen_2234_);
lean_ctor_set(v_reuseFailAlloc_2252_, 4, v_traceState_2235_);
lean_ctor_set(v_reuseFailAlloc_2252_, 5, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2252_, 6, v_recordedDeps_2236_);
lean_ctor_set(v_reuseFailAlloc_2252_, 7, v_messages_2237_);
lean_ctor_set(v_reuseFailAlloc_2252_, 8, v_infoState_2238_);
lean_ctor_set(v_reuseFailAlloc_2252_, 9, v_snapshotTasks_2239_);
v___x_2247_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = lean_st_ref_put(v_a_2212_, v___x_2247_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2243_);
v___x_2250_ = v___x_2227_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2243_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v_ext_2209_);
v_a_2256_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2224_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2224_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_dec(v_declName_2210_);
lean_dec_ref(v_ext_2209_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_2264_, lean_object* v_declName_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2264_, v_declName_2265_, v_a_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_2270_, lean_object* v_s_2271_){
_start:
{
lean_object* v_casesTypes_2272_; lean_object* v_extThms_2273_; lean_object* v_ematch_2274_; lean_object* v_inj_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_casesTypes_2272_ = lean_ctor_get(v_s_2271_, 0);
v_extThms_2273_ = lean_ctor_get(v_s_2271_, 1);
v_ematch_2274_ = lean_ctor_get(v_s_2271_, 3);
v_inj_2275_ = lean_ctor_get(v_s_2271_, 4);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_s_2271_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v_s_2271_, 2);
lean_dec(v_unused_2283_);
v___x_2277_ = v_s_2271_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_inj_2275_);
lean_inc(v_ematch_2274_);
lean_inc(v_extThms_2273_);
lean_inc(v_casesTypes_2272_);
lean_dec(v_s_2271_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 2, v___x_2270_);
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_casesTypes_2272_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_extThms_2273_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_ematch_2274_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_inj_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_2284_, lean_object* v_t_2285_){
_start:
{
if (lean_obj_tag(v_t_2285_) == 0)
{
lean_object* v_k_2286_; lean_object* v_v_2287_; lean_object* v_l_2288_; lean_object* v_r_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2943_; 
v_k_2286_ = lean_ctor_get(v_t_2285_, 1);
v_v_2287_ = lean_ctor_get(v_t_2285_, 2);
v_l_2288_ = lean_ctor_get(v_t_2285_, 3);
v_r_2289_ = lean_ctor_get(v_t_2285_, 4);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_t_2285_);
if (v_isSharedCheck_2943_ == 0)
{
lean_object* v_unused_2944_; 
v_unused_2944_ = lean_ctor_get(v_t_2285_, 0);
lean_dec(v_unused_2944_);
v___x_2291_ = v_t_2285_;
v_isShared_2292_ = v_isSharedCheck_2943_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_r_2289_);
lean_inc(v_l_2288_);
lean_inc(v_v_2287_);
lean_inc(v_k_2286_);
lean_dec(v_t_2285_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2943_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
uint8_t v___x_2293_; 
v___x_2293_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2284_, v_k_2286_);
switch(v___x_2293_)
{
case 0:
{
lean_object* v_impl_2294_; lean_object* v___x_2295_; 
v_impl_2294_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2284_, v_l_2288_);
v___x_2295_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2294_) == 0)
{
if (lean_obj_tag(v_r_2289_) == 0)
{
lean_object* v_size_2296_; lean_object* v_size_2297_; lean_object* v_k_2298_; lean_object* v_v_2299_; lean_object* v_l_2300_; lean_object* v_r_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v_size_2296_ = lean_ctor_get(v_impl_2294_, 0);
v_size_2297_ = lean_ctor_get(v_r_2289_, 0);
v_k_2298_ = lean_ctor_get(v_r_2289_, 1);
v_v_2299_ = lean_ctor_get(v_r_2289_, 2);
v_l_2300_ = lean_ctor_get(v_r_2289_, 3);
lean_inc(v_l_2300_);
v_r_2301_ = lean_ctor_get(v_r_2289_, 4);
v___x_2302_ = lean_unsigned_to_nat(3u);
v___x_2303_ = lean_nat_mul(v___x_2302_, v_size_2296_);
v___x_2304_ = lean_nat_dec_lt(v___x_2303_, v_size_2297_);
lean_dec(v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
lean_dec(v_l_2300_);
v___x_2305_ = lean_nat_add(v___x_2295_, v_size_2296_);
v___x_2306_ = lean_nat_add(v___x_2305_, v_size_2297_);
lean_dec(v___x_2305_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 3, v_impl_2294_);
lean_ctor_set(v___x_2291_, 0, v___x_2306_);
v___x_2308_ = v___x_2291_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_impl_2294_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v_r_2289_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
else
{
lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2373_; 
lean_inc(v_r_2301_);
lean_inc(v_v_2299_);
lean_inc(v_k_2298_);
lean_inc(v_size_2297_);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_r_2289_);
if (v_isSharedCheck_2373_ == 0)
{
lean_object* v_unused_2374_; lean_object* v_unused_2375_; lean_object* v_unused_2376_; lean_object* v_unused_2377_; lean_object* v_unused_2378_; 
v_unused_2374_ = lean_ctor_get(v_r_2289_, 4);
lean_dec(v_unused_2374_);
v_unused_2375_ = lean_ctor_get(v_r_2289_, 3);
lean_dec(v_unused_2375_);
v_unused_2376_ = lean_ctor_get(v_r_2289_, 2);
lean_dec(v_unused_2376_);
v_unused_2377_ = lean_ctor_get(v_r_2289_, 1);
lean_dec(v_unused_2377_);
v_unused_2378_ = lean_ctor_get(v_r_2289_, 0);
lean_dec(v_unused_2378_);
v___x_2311_ = v_r_2289_;
v_isShared_2312_ = v_isSharedCheck_2373_;
goto v_resetjp_2310_;
}
else
{
lean_dec(v_r_2289_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2373_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v_size_2313_; lean_object* v_k_2314_; lean_object* v_v_2315_; lean_object* v_l_2316_; lean_object* v_r_2317_; lean_object* v_size_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_size_2313_ = lean_ctor_get(v_l_2300_, 0);
v_k_2314_ = lean_ctor_get(v_l_2300_, 1);
v_v_2315_ = lean_ctor_get(v_l_2300_, 2);
v_l_2316_ = lean_ctor_get(v_l_2300_, 3);
v_r_2317_ = lean_ctor_get(v_l_2300_, 4);
v_size_2318_ = lean_ctor_get(v_r_2301_, 0);
v___x_2319_ = lean_unsigned_to_nat(2u);
v___x_2320_ = lean_nat_mul(v___x_2319_, v_size_2318_);
v___x_2321_ = lean_nat_dec_lt(v_size_2313_, v___x_2320_);
lean_dec(v___x_2320_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2349_; 
lean_inc(v_r_2317_);
lean_inc(v_l_2316_);
lean_inc(v_v_2315_);
lean_inc(v_k_2314_);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_l_2300_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; lean_object* v_unused_2351_; lean_object* v_unused_2352_; lean_object* v_unused_2353_; lean_object* v_unused_2354_; 
v_unused_2350_ = lean_ctor_get(v_l_2300_, 4);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_l_2300_, 3);
lean_dec(v_unused_2351_);
v_unused_2352_ = lean_ctor_get(v_l_2300_, 2);
lean_dec(v_unused_2352_);
v_unused_2353_ = lean_ctor_get(v_l_2300_, 1);
lean_dec(v_unused_2353_);
v_unused_2354_ = lean_ctor_get(v_l_2300_, 0);
lean_dec(v_unused_2354_);
v___x_2323_ = v_l_2300_;
v_isShared_2324_ = v_isSharedCheck_2349_;
goto v_resetjp_2322_;
}
else
{
lean_dec(v_l_2300_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2349_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2339_; 
v___x_2325_ = lean_nat_add(v___x_2295_, v_size_2296_);
v___x_2326_ = lean_nat_add(v___x_2325_, v_size_2297_);
lean_dec(v_size_2297_);
if (lean_obj_tag(v_l_2316_) == 0)
{
lean_object* v_size_2347_; 
v_size_2347_ = lean_ctor_get(v_l_2316_, 0);
lean_inc(v_size_2347_);
v___y_2339_ = v_size_2347_;
goto v___jp_2338_;
}
else
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_unsigned_to_nat(0u);
v___y_2339_ = v___x_2348_;
goto v___jp_2338_;
}
v___jp_2327_:
{
lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2331_ = lean_nat_add(v___y_2328_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec(v___y_2328_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 4, v_r_2301_);
lean_ctor_set(v___x_2323_, 3, v_r_2317_);
lean_ctor_set(v___x_2323_, 2, v_v_2299_);
lean_ctor_set(v___x_2323_, 1, v_k_2298_);
lean_ctor_set(v___x_2323_, 0, v___x_2331_);
v___x_2333_ = v___x_2323_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_k_2298_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_v_2299_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_r_2317_);
lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_r_2301_);
v___x_2333_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 4, v___x_2333_);
lean_ctor_set(v___x_2311_, 3, v___y_2329_);
lean_ctor_set(v___x_2311_, 2, v_v_2315_);
lean_ctor_set(v___x_2311_, 1, v_k_2314_);
lean_ctor_set(v___x_2311_, 0, v___x_2326_);
v___x_2335_ = v___x_2311_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_k_2314_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_v_2315_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v___y_2329_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
v___jp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2340_ = lean_nat_add(v___x_2325_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec(v___x_2325_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v_l_2316_);
lean_ctor_set(v___x_2291_, 3, v_impl_2294_);
lean_ctor_set(v___x_2291_, 0, v___x_2340_);
v___x_2342_ = v___x_2291_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_impl_2294_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_l_2316_);
v___x_2342_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_nat_add(v___x_2295_, v_size_2318_);
if (lean_obj_tag(v_r_2317_) == 0)
{
lean_object* v_size_2344_; 
v_size_2344_ = lean_ctor_get(v_r_2317_, 0);
lean_inc(v_size_2344_);
v___y_2328_ = v___x_2343_;
v___y_2329_ = v___x_2342_;
v___y_2330_ = v_size_2344_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_unsigned_to_nat(0u);
v___y_2328_ = v___x_2343_;
v___y_2329_ = v___x_2342_;
v___y_2330_ = v___x_2345_;
goto v___jp_2327_;
}
}
}
}
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
lean_del_object(v___x_2291_);
v___x_2355_ = lean_nat_add(v___x_2295_, v_size_2296_);
v___x_2356_ = lean_nat_add(v___x_2355_, v_size_2297_);
lean_dec(v_size_2297_);
v___x_2357_ = lean_nat_add(v___x_2355_, v_size_2313_);
lean_dec(v___x_2355_);
lean_inc_ref(v_impl_2294_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 4, v_l_2300_);
lean_ctor_set(v___x_2311_, 3, v_impl_2294_);
lean_ctor_set(v___x_2311_, 2, v_v_2287_);
lean_ctor_set(v___x_2311_, 1, v_k_2286_);
lean_ctor_set(v___x_2311_, 0, v___x_2357_);
v___x_2359_ = v___x_2311_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2372_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2372_, 3, v_impl_2294_);
lean_ctor_set(v_reuseFailAlloc_2372_, 4, v_l_2300_);
v___x_2359_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
v_isSharedCheck_2366_ = !lean_is_exclusive(v_impl_2294_);
if (v_isSharedCheck_2366_ == 0)
{
lean_object* v_unused_2367_; lean_object* v_unused_2368_; lean_object* v_unused_2369_; lean_object* v_unused_2370_; lean_object* v_unused_2371_; 
v_unused_2367_ = lean_ctor_get(v_impl_2294_, 4);
lean_dec(v_unused_2367_);
v_unused_2368_ = lean_ctor_get(v_impl_2294_, 3);
lean_dec(v_unused_2368_);
v_unused_2369_ = lean_ctor_get(v_impl_2294_, 2);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_impl_2294_, 1);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v_impl_2294_, 0);
lean_dec(v_unused_2371_);
v___x_2361_ = v_impl_2294_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_dec(v_impl_2294_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 4, v_r_2301_);
lean_ctor_set(v___x_2361_, 3, v___x_2359_);
lean_ctor_set(v___x_2361_, 2, v_v_2299_);
lean_ctor_set(v___x_2361_, 1, v_k_2298_);
lean_ctor_set(v___x_2361_, 0, v___x_2356_);
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_k_2298_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_v_2299_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_r_2301_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v_size_2379_ = lean_ctor_get(v_impl_2294_, 0);
v___x_2380_ = lean_nat_add(v___x_2295_, v_size_2379_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 3, v_impl_2294_);
lean_ctor_set(v___x_2291_, 0, v___x_2380_);
v___x_2382_ = v___x_2291_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2383_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2383_, 3, v_impl_2294_);
lean_ctor_set(v_reuseFailAlloc_2383_, 4, v_r_2289_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
else
{
if (lean_obj_tag(v_r_2289_) == 0)
{
lean_object* v_l_2384_; 
v_l_2384_ = lean_ctor_get(v_r_2289_, 3);
lean_inc(v_l_2384_);
if (lean_obj_tag(v_l_2384_) == 0)
{
lean_object* v_r_2385_; 
v_r_2385_ = lean_ctor_get(v_r_2289_, 4);
lean_inc(v_r_2385_);
if (lean_obj_tag(v_r_2385_) == 0)
{
lean_object* v_size_2386_; lean_object* v_k_2387_; lean_object* v_v_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2401_; 
v_size_2386_ = lean_ctor_get(v_r_2289_, 0);
v_k_2387_ = lean_ctor_get(v_r_2289_, 1);
v_v_2388_ = lean_ctor_get(v_r_2289_, 2);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_r_2289_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; lean_object* v_unused_2403_; 
v_unused_2402_ = lean_ctor_get(v_r_2289_, 4);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_r_2289_, 3);
lean_dec(v_unused_2403_);
v___x_2390_ = v_r_2289_;
v_isShared_2391_ = v_isSharedCheck_2401_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_v_2388_);
lean_inc(v_k_2387_);
lean_inc(v_size_2386_);
lean_dec(v_r_2289_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2401_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v_size_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
v_size_2392_ = lean_ctor_get(v_l_2384_, 0);
v___x_2393_ = lean_nat_add(v___x_2295_, v_size_2386_);
lean_dec(v_size_2386_);
v___x_2394_ = lean_nat_add(v___x_2295_, v_size_2392_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 4, v_l_2384_);
lean_ctor_set(v___x_2390_, 3, v_impl_2294_);
lean_ctor_set(v___x_2390_, 2, v_v_2287_);
lean_ctor_set(v___x_2390_, 1, v_k_2286_);
lean_ctor_set(v___x_2390_, 0, v___x_2394_);
v___x_2396_ = v___x_2390_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_impl_2294_);
lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_l_2384_);
v___x_2396_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2398_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v_r_2385_);
lean_ctor_set(v___x_2291_, 3, v___x_2396_);
lean_ctor_set(v___x_2291_, 2, v_v_2388_);
lean_ctor_set(v___x_2291_, 1, v_k_2387_);
lean_ctor_set(v___x_2291_, 0, v___x_2393_);
v___x_2398_ = v___x_2291_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_k_2387_);
lean_ctor_set(v_reuseFailAlloc_2399_, 2, v_v_2388_);
lean_ctor_set(v_reuseFailAlloc_2399_, 3, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2399_, 4, v_r_2385_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
else
{
lean_object* v_k_2404_; lean_object* v_v_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2428_; 
v_k_2404_ = lean_ctor_get(v_r_2289_, 1);
v_v_2405_ = lean_ctor_get(v_r_2289_, 2);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_r_2289_);
if (v_isSharedCheck_2428_ == 0)
{
lean_object* v_unused_2429_; lean_object* v_unused_2430_; lean_object* v_unused_2431_; 
v_unused_2429_ = lean_ctor_get(v_r_2289_, 4);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_r_2289_, 3);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_r_2289_, 0);
lean_dec(v_unused_2431_);
v___x_2407_ = v_r_2289_;
v_isShared_2408_ = v_isSharedCheck_2428_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_v_2405_);
lean_inc(v_k_2404_);
lean_dec(v_r_2289_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2428_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v_k_2409_; lean_object* v_v_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2424_; 
v_k_2409_ = lean_ctor_get(v_l_2384_, 1);
v_v_2410_ = lean_ctor_get(v_l_2384_, 2);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_l_2384_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; lean_object* v_unused_2426_; lean_object* v_unused_2427_; 
v_unused_2425_ = lean_ctor_get(v_l_2384_, 4);
lean_dec(v_unused_2425_);
v_unused_2426_ = lean_ctor_get(v_l_2384_, 3);
lean_dec(v_unused_2426_);
v_unused_2427_ = lean_ctor_get(v_l_2384_, 0);
lean_dec(v_unused_2427_);
v___x_2412_ = v_l_2384_;
v_isShared_2413_ = v_isSharedCheck_2424_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
lean_dec(v_l_2384_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2424_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = lean_unsigned_to_nat(3u);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 4, v_r_2385_);
lean_ctor_set(v___x_2412_, 3, v_r_2385_);
lean_ctor_set(v___x_2412_, 2, v_v_2287_);
lean_ctor_set(v___x_2412_, 1, v_k_2286_);
lean_ctor_set(v___x_2412_, 0, v___x_2295_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_r_2385_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_r_2385_);
v___x_2416_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2418_; 
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 3, v_r_2385_);
lean_ctor_set(v___x_2407_, 0, v___x_2295_);
v___x_2418_ = v___x_2407_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_k_2404_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_v_2405_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_r_2385_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v_r_2385_);
v___x_2418_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2420_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v___x_2418_);
lean_ctor_set(v___x_2291_, 3, v___x_2416_);
lean_ctor_set(v___x_2291_, 2, v_v_2410_);
lean_ctor_set(v___x_2291_, 1, v_k_2409_);
lean_ctor_set(v___x_2291_, 0, v___x_2414_);
v___x_2420_ = v___x_2291_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2421_, 3, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2421_, 4, v___x_2418_);
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
}
}
}
else
{
lean_object* v_r_2432_; 
v_r_2432_ = lean_ctor_get(v_r_2289_, 4);
lean_inc(v_r_2432_);
if (lean_obj_tag(v_r_2432_) == 0)
{
lean_object* v_k_2433_; lean_object* v_v_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2445_; 
v_k_2433_ = lean_ctor_get(v_r_2289_, 1);
v_v_2434_ = lean_ctor_get(v_r_2289_, 2);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_r_2289_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; lean_object* v_unused_2447_; lean_object* v_unused_2448_; 
v_unused_2446_ = lean_ctor_get(v_r_2289_, 4);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_r_2289_, 3);
lean_dec(v_unused_2447_);
v_unused_2448_ = lean_ctor_get(v_r_2289_, 0);
lean_dec(v_unused_2448_);
v___x_2436_ = v_r_2289_;
v_isShared_2437_ = v_isSharedCheck_2445_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_v_2434_);
lean_inc(v_k_2433_);
lean_dec(v_r_2289_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2445_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = lean_unsigned_to_nat(3u);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 4, v_l_2384_);
lean_ctor_set(v___x_2436_, 2, v_v_2287_);
lean_ctor_set(v___x_2436_, 1, v_k_2286_);
lean_ctor_set(v___x_2436_, 0, v___x_2295_);
v___x_2440_ = v___x_2436_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2444_, 3, v_l_2384_);
lean_ctor_set(v_reuseFailAlloc_2444_, 4, v_l_2384_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2442_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v_r_2432_);
lean_ctor_set(v___x_2291_, 3, v___x_2440_);
lean_ctor_set(v___x_2291_, 2, v_v_2434_);
lean_ctor_set(v___x_2291_, 1, v_k_2433_);
lean_ctor_set(v___x_2291_, 0, v___x_2438_);
v___x_2442_ = v___x_2291_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_k_2433_);
lean_ctor_set(v_reuseFailAlloc_2443_, 2, v_v_2434_);
lean_ctor_set(v_reuseFailAlloc_2443_, 3, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2443_, 4, v_r_2432_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_object* v_size_2449_; lean_object* v_k_2450_; lean_object* v_v_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2462_; 
v_size_2449_ = lean_ctor_get(v_r_2289_, 0);
v_k_2450_ = lean_ctor_get(v_r_2289_, 1);
v_v_2451_ = lean_ctor_get(v_r_2289_, 2);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_r_2289_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; lean_object* v_unused_2464_; 
v_unused_2463_ = lean_ctor_get(v_r_2289_, 4);
lean_dec(v_unused_2463_);
v_unused_2464_ = lean_ctor_get(v_r_2289_, 3);
lean_dec(v_unused_2464_);
v___x_2453_ = v_r_2289_;
v_isShared_2454_ = v_isSharedCheck_2462_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_v_2451_);
lean_inc(v_k_2450_);
lean_inc(v_size_2449_);
lean_dec(v_r_2289_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2462_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 3, v_r_2432_);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_size_2449_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_k_2450_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_v_2451_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v_r_2432_);
lean_ctor_set(v_reuseFailAlloc_2461_, 4, v_r_2432_);
v___x_2456_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2457_ = lean_unsigned_to_nat(2u);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v___x_2456_);
lean_ctor_set(v___x_2291_, 3, v_r_2432_);
lean_ctor_set(v___x_2291_, 0, v___x_2457_);
v___x_2459_ = v___x_2291_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v_r_2432_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v___x_2456_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
}
else
{
lean_object* v___x_2466_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 3, v_r_2289_);
lean_ctor_set(v___x_2291_, 0, v___x_2295_);
v___x_2466_ = v___x_2291_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v_r_2289_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v_r_2289_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2291_);
lean_dec(v_v_2287_);
lean_dec(v_k_2286_);
if (lean_obj_tag(v_l_2288_) == 0)
{
if (lean_obj_tag(v_r_2289_) == 0)
{
lean_object* v_size_2468_; lean_object* v_k_2469_; lean_object* v_v_2470_; lean_object* v_l_2471_; lean_object* v_r_2472_; lean_object* v_size_2473_; lean_object* v_k_2474_; lean_object* v_v_2475_; lean_object* v_l_2476_; lean_object* v_r_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v_size_2468_ = lean_ctor_get(v_l_2288_, 0);
v_k_2469_ = lean_ctor_get(v_l_2288_, 1);
v_v_2470_ = lean_ctor_get(v_l_2288_, 2);
v_l_2471_ = lean_ctor_get(v_l_2288_, 3);
v_r_2472_ = lean_ctor_get(v_l_2288_, 4);
lean_inc(v_r_2472_);
v_size_2473_ = lean_ctor_get(v_r_2289_, 0);
v_k_2474_ = lean_ctor_get(v_r_2289_, 1);
v_v_2475_ = lean_ctor_get(v_r_2289_, 2);
v_l_2476_ = lean_ctor_get(v_r_2289_, 3);
lean_inc(v_l_2476_);
v_r_2477_ = lean_ctor_get(v_r_2289_, 4);
v___x_2478_ = lean_unsigned_to_nat(1u);
v___x_2479_ = lean_nat_dec_lt(v_size_2468_, v_size_2473_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2615_; 
lean_inc(v_l_2471_);
lean_inc(v_v_2470_);
lean_inc(v_k_2469_);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_l_2288_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; lean_object* v_unused_2617_; lean_object* v_unused_2618_; lean_object* v_unused_2619_; lean_object* v_unused_2620_; 
v_unused_2616_ = lean_ctor_get(v_l_2288_, 4);
lean_dec(v_unused_2616_);
v_unused_2617_ = lean_ctor_get(v_l_2288_, 3);
lean_dec(v_unused_2617_);
v_unused_2618_ = lean_ctor_get(v_l_2288_, 2);
lean_dec(v_unused_2618_);
v_unused_2619_ = lean_ctor_get(v_l_2288_, 1);
lean_dec(v_unused_2619_);
v_unused_2620_ = lean_ctor_get(v_l_2288_, 0);
lean_dec(v_unused_2620_);
v___x_2481_ = v_l_2288_;
v_isShared_2482_ = v_isSharedCheck_2615_;
goto v_resetjp_2480_;
}
else
{
lean_dec(v_l_2288_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2615_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v_tree_2484_; 
v___x_2483_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2469_, v_v_2470_, v_l_2471_, v_r_2472_);
v_tree_2484_ = lean_ctor_get(v___x_2483_, 2);
if (lean_obj_tag(v_tree_2484_) == 0)
{
lean_object* v_k_2485_; lean_object* v_v_2486_; lean_object* v_size_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
lean_inc_ref(v_tree_2484_);
v_k_2485_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_k_2485_);
v_v_2486_ = lean_ctor_get(v___x_2483_, 1);
lean_inc(v_v_2486_);
lean_dec_ref(v___x_2483_);
v_size_2487_ = lean_ctor_get(v_tree_2484_, 0);
v___x_2488_ = lean_unsigned_to_nat(3u);
v___x_2489_ = lean_nat_mul(v___x_2488_, v_size_2487_);
v___x_2490_ = lean_nat_dec_lt(v___x_2489_, v_size_2473_);
lean_dec(v___x_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2494_; 
lean_dec(v_l_2476_);
v___x_2491_ = lean_nat_add(v___x_2478_, v_size_2487_);
v___x_2492_ = lean_nat_add(v___x_2491_, v_size_2473_);
lean_dec(v___x_2491_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v_r_2289_);
lean_ctor_set(v___x_2481_, 3, v_tree_2484_);
lean_ctor_set(v___x_2481_, 2, v_v_2486_);
lean_ctor_set(v___x_2481_, 1, v_k_2485_);
lean_ctor_set(v___x_2481_, 0, v___x_2492_);
v___x_2494_ = v___x_2481_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_k_2485_);
lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_v_2486_);
lean_ctor_set(v_reuseFailAlloc_2495_, 3, v_tree_2484_);
lean_ctor_set(v_reuseFailAlloc_2495_, 4, v_r_2289_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
else
{
lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2550_; 
lean_inc(v_r_2477_);
lean_inc(v_v_2475_);
lean_inc(v_k_2474_);
lean_inc(v_size_2473_);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_r_2289_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; lean_object* v_unused_2552_; lean_object* v_unused_2553_; lean_object* v_unused_2554_; lean_object* v_unused_2555_; 
v_unused_2551_ = lean_ctor_get(v_r_2289_, 4);
lean_dec(v_unused_2551_);
v_unused_2552_ = lean_ctor_get(v_r_2289_, 3);
lean_dec(v_unused_2552_);
v_unused_2553_ = lean_ctor_get(v_r_2289_, 2);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_r_2289_, 1);
lean_dec(v_unused_2554_);
v_unused_2555_ = lean_ctor_get(v_r_2289_, 0);
lean_dec(v_unused_2555_);
v___x_2497_ = v_r_2289_;
v_isShared_2498_ = v_isSharedCheck_2550_;
goto v_resetjp_2496_;
}
else
{
lean_dec(v_r_2289_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2550_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v_size_2499_; lean_object* v_k_2500_; lean_object* v_v_2501_; lean_object* v_l_2502_; lean_object* v_r_2503_; lean_object* v_size_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v_size_2499_ = lean_ctor_get(v_l_2476_, 0);
v_k_2500_ = lean_ctor_get(v_l_2476_, 1);
v_v_2501_ = lean_ctor_get(v_l_2476_, 2);
v_l_2502_ = lean_ctor_get(v_l_2476_, 3);
v_r_2503_ = lean_ctor_get(v_l_2476_, 4);
v_size_2504_ = lean_ctor_get(v_r_2477_, 0);
v___x_2505_ = lean_unsigned_to_nat(2u);
v___x_2506_ = lean_nat_mul(v___x_2505_, v_size_2504_);
v___x_2507_ = lean_nat_dec_lt(v_size_2499_, v___x_2506_);
lean_dec(v___x_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2535_; 
lean_inc(v_r_2503_);
lean_inc(v_l_2502_);
lean_inc(v_v_2501_);
lean_inc(v_k_2500_);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_l_2476_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; 
v_unused_2536_ = lean_ctor_get(v_l_2476_, 4);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_l_2476_, 3);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_l_2476_, 2);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_l_2476_, 1);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_l_2476_, 0);
lean_dec(v_unused_2540_);
v___x_2509_ = v_l_2476_;
v_isShared_2510_ = v_isSharedCheck_2535_;
goto v_resetjp_2508_;
}
else
{
lean_dec(v_l_2476_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2535_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2525_; 
v___x_2511_ = lean_nat_add(v___x_2478_, v_size_2487_);
v___x_2512_ = lean_nat_add(v___x_2511_, v_size_2473_);
lean_dec(v_size_2473_);
if (lean_obj_tag(v_l_2502_) == 0)
{
lean_object* v_size_2533_; 
v_size_2533_ = lean_ctor_get(v_l_2502_, 0);
lean_inc(v_size_2533_);
v___y_2525_ = v_size_2533_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_unsigned_to_nat(0u);
v___y_2525_ = v___x_2534_;
goto v___jp_2524_;
}
v___jp_2513_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_nat_add(v___y_2514_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec(v___y_2514_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 4, v_r_2477_);
lean_ctor_set(v___x_2509_, 3, v_r_2503_);
lean_ctor_set(v___x_2509_, 2, v_v_2475_);
lean_ctor_set(v___x_2509_, 1, v_k_2474_);
lean_ctor_set(v___x_2509_, 0, v___x_2517_);
v___x_2519_ = v___x_2509_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v_r_2503_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_r_2477_);
v___x_2519_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2521_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 4, v___x_2519_);
lean_ctor_set(v___x_2497_, 3, v___y_2515_);
lean_ctor_set(v___x_2497_, 2, v_v_2501_);
lean_ctor_set(v___x_2497_, 1, v_k_2500_);
lean_ctor_set(v___x_2497_, 0, v___x_2512_);
v___x_2521_ = v___x_2497_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_k_2500_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_v_2501_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v___y_2515_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
v___jp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2526_ = lean_nat_add(v___x_2511_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec(v___x_2511_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v_l_2502_);
lean_ctor_set(v___x_2481_, 3, v_tree_2484_);
lean_ctor_set(v___x_2481_, 2, v_v_2486_);
lean_ctor_set(v___x_2481_, 1, v_k_2485_);
lean_ctor_set(v___x_2481_, 0, v___x_2526_);
v___x_2528_ = v___x_2481_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_k_2485_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_v_2486_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_tree_2484_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_l_2502_);
v___x_2528_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_nat_add(v___x_2478_, v_size_2504_);
if (lean_obj_tag(v_r_2503_) == 0)
{
lean_object* v_size_2530_; 
v_size_2530_ = lean_ctor_get(v_r_2503_, 0);
lean_inc(v_size_2530_);
v___y_2514_ = v___x_2529_;
v___y_2515_ = v___x_2528_;
v___y_2516_ = v_size_2530_;
goto v___jp_2513_;
}
else
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v___y_2514_ = v___x_2529_;
v___y_2515_ = v___x_2528_;
v___y_2516_ = v___x_2531_;
goto v___jp_2513_;
}
}
}
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2541_ = lean_nat_add(v___x_2478_, v_size_2487_);
v___x_2542_ = lean_nat_add(v___x_2541_, v_size_2473_);
lean_dec(v_size_2473_);
v___x_2543_ = lean_nat_add(v___x_2541_, v_size_2499_);
lean_dec(v___x_2541_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 4, v_l_2476_);
lean_ctor_set(v___x_2497_, 3, v_tree_2484_);
lean_ctor_set(v___x_2497_, 2, v_v_2486_);
lean_ctor_set(v___x_2497_, 1, v_k_2485_);
lean_ctor_set(v___x_2497_, 0, v___x_2543_);
v___x_2545_ = v___x_2497_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_k_2485_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_v_2486_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_tree_2484_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v_l_2476_);
v___x_2545_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v_r_2477_);
lean_ctor_set(v___x_2481_, 3, v___x_2545_);
lean_ctor_set(v___x_2481_, 2, v_v_2475_);
lean_ctor_set(v___x_2481_, 1, v_k_2474_);
lean_ctor_set(v___x_2481_, 0, v___x_2542_);
v___x_2547_ = v___x_2481_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v_r_2477_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
else
{
lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2609_; 
lean_inc(v_r_2477_);
lean_inc(v_v_2475_);
lean_inc(v_k_2474_);
lean_inc(v_size_2473_);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_r_2289_);
if (v_isSharedCheck_2609_ == 0)
{
lean_object* v_unused_2610_; lean_object* v_unused_2611_; lean_object* v_unused_2612_; lean_object* v_unused_2613_; lean_object* v_unused_2614_; 
v_unused_2610_ = lean_ctor_get(v_r_2289_, 4);
lean_dec(v_unused_2610_);
v_unused_2611_ = lean_ctor_get(v_r_2289_, 3);
lean_dec(v_unused_2611_);
v_unused_2612_ = lean_ctor_get(v_r_2289_, 2);
lean_dec(v_unused_2612_);
v_unused_2613_ = lean_ctor_get(v_r_2289_, 1);
lean_dec(v_unused_2613_);
v_unused_2614_ = lean_ctor_get(v_r_2289_, 0);
lean_dec(v_unused_2614_);
v___x_2557_ = v_r_2289_;
v_isShared_2558_ = v_isSharedCheck_2609_;
goto v_resetjp_2556_;
}
else
{
lean_dec(v_r_2289_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2609_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
if (lean_obj_tag(v_l_2476_) == 0)
{
if (lean_obj_tag(v_r_2477_) == 0)
{
lean_object* v_k_2559_; lean_object* v_v_2560_; lean_object* v_size_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
lean_inc(v_tree_2484_);
v_k_2559_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_k_2559_);
v_v_2560_ = lean_ctor_get(v___x_2483_, 1);
lean_inc(v_v_2560_);
lean_dec_ref(v___x_2483_);
v_size_2561_ = lean_ctor_get(v_l_2476_, 0);
v___x_2562_ = lean_nat_add(v___x_2478_, v_size_2473_);
lean_dec(v_size_2473_);
v___x_2563_ = lean_nat_add(v___x_2478_, v_size_2561_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v_l_2476_);
lean_ctor_set(v___x_2557_, 3, v_tree_2484_);
lean_ctor_set(v___x_2557_, 2, v_v_2560_);
lean_ctor_set(v___x_2557_, 1, v_k_2559_);
lean_ctor_set(v___x_2557_, 0, v___x_2563_);
v___x_2565_ = v___x_2557_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2563_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_k_2559_);
lean_ctor_set(v_reuseFailAlloc_2569_, 2, v_v_2560_);
lean_ctor_set(v_reuseFailAlloc_2569_, 3, v_tree_2484_);
lean_ctor_set(v_reuseFailAlloc_2569_, 4, v_l_2476_);
v___x_2565_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2567_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v_r_2477_);
lean_ctor_set(v___x_2481_, 3, v___x_2565_);
lean_ctor_set(v___x_2481_, 2, v_v_2475_);
lean_ctor_set(v___x_2481_, 1, v_k_2474_);
lean_ctor_set(v___x_2481_, 0, v___x_2562_);
v___x_2567_ = v___x_2481_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2568_, 3, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2568_, 4, v_r_2477_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
lean_object* v_k_2570_; lean_object* v_v_2571_; lean_object* v_k_2572_; lean_object* v_v_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v_size_2473_);
v_k_2570_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_k_2570_);
v_v_2571_ = lean_ctor_get(v___x_2483_, 1);
lean_inc(v_v_2571_);
lean_dec_ref(v___x_2483_);
v_k_2572_ = lean_ctor_get(v_l_2476_, 1);
v_v_2573_ = lean_ctor_get(v_l_2476_, 2);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_l_2476_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; lean_object* v_unused_2589_; lean_object* v_unused_2590_; 
v_unused_2588_ = lean_ctor_get(v_l_2476_, 4);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v_l_2476_, 3);
lean_dec(v_unused_2589_);
v_unused_2590_ = lean_ctor_get(v_l_2476_, 0);
lean_dec(v_unused_2590_);
v___x_2575_ = v_l_2476_;
v_isShared_2576_ = v_isSharedCheck_2587_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_v_2573_);
lean_inc(v_k_2572_);
lean_dec(v_l_2476_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2587_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_unsigned_to_nat(3u);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_r_2477_);
lean_ctor_set(v___x_2575_, 3, v_r_2477_);
lean_ctor_set(v___x_2575_, 2, v_v_2571_);
lean_ctor_set(v___x_2575_, 1, v_k_2570_);
lean_ctor_set(v___x_2575_, 0, v___x_2478_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_r_2477_);
lean_ctor_set(v_reuseFailAlloc_2586_, 4, v_r_2477_);
v___x_2579_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 3, v_r_2477_);
lean_ctor_set(v___x_2557_, 0, v___x_2478_);
v___x_2581_ = v___x_2557_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_r_2477_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_r_2477_);
v___x_2581_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2583_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v___x_2581_);
lean_ctor_set(v___x_2481_, 3, v___x_2579_);
lean_ctor_set(v___x_2481_, 2, v_v_2573_);
lean_ctor_set(v___x_2481_, 1, v_k_2572_);
lean_ctor_set(v___x_2481_, 0, v___x_2577_);
v___x_2583_ = v___x_2481_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_k_2572_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_v_2573_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2477_) == 0)
{
lean_object* v_k_2591_; lean_object* v_v_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_dec(v_size_2473_);
v_k_2591_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_k_2591_);
v_v_2592_ = lean_ctor_get(v___x_2483_, 1);
lean_inc(v_v_2592_);
lean_dec_ref(v___x_2483_);
v___x_2593_ = lean_unsigned_to_nat(3u);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v_l_2476_);
lean_ctor_set(v___x_2557_, 2, v_v_2592_);
lean_ctor_set(v___x_2557_, 1, v_k_2591_);
lean_ctor_set(v___x_2557_, 0, v___x_2478_);
v___x_2595_ = v___x_2557_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_k_2591_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_v_2592_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v_l_2476_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v_l_2476_);
v___x_2595_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v_r_2477_);
lean_ctor_set(v___x_2481_, 3, v___x_2595_);
lean_ctor_set(v___x_2481_, 2, v_v_2475_);
lean_ctor_set(v___x_2481_, 1, v_k_2474_);
lean_ctor_set(v___x_2481_, 0, v___x_2593_);
v___x_2597_ = v___x_2481_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v_r_2477_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
else
{
lean_object* v_k_2600_; lean_object* v_v_2601_; lean_object* v___x_2603_; 
v_k_2600_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_k_2600_);
v_v_2601_ = lean_ctor_get(v___x_2483_, 1);
lean_inc(v_v_2601_);
lean_dec_ref(v___x_2483_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 3, v_r_2477_);
v___x_2603_ = v___x_2557_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_size_2473_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2608_, 3, v_r_2477_);
lean_ctor_set(v_reuseFailAlloc_2608_, 4, v_r_2477_);
v___x_2603_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2604_ = lean_unsigned_to_nat(2u);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v___x_2603_);
lean_ctor_set(v___x_2481_, 3, v_r_2477_);
lean_ctor_set(v___x_2481_, 2, v_v_2601_);
lean_ctor_set(v___x_2481_, 1, v_k_2600_);
lean_ctor_set(v___x_2481_, 0, v___x_2604_);
v___x_2606_ = v___x_2481_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_k_2600_);
lean_ctor_set(v_reuseFailAlloc_2607_, 2, v_v_2601_);
lean_ctor_set(v_reuseFailAlloc_2607_, 3, v_r_2477_);
lean_ctor_set(v_reuseFailAlloc_2607_, 4, v___x_2603_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
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
lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2773_; 
lean_inc(v_r_2477_);
lean_inc(v_v_2475_);
lean_inc(v_k_2474_);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_r_2289_);
if (v_isSharedCheck_2773_ == 0)
{
lean_object* v_unused_2774_; lean_object* v_unused_2775_; lean_object* v_unused_2776_; lean_object* v_unused_2777_; lean_object* v_unused_2778_; 
v_unused_2774_ = lean_ctor_get(v_r_2289_, 4);
lean_dec(v_unused_2774_);
v_unused_2775_ = lean_ctor_get(v_r_2289_, 3);
lean_dec(v_unused_2775_);
v_unused_2776_ = lean_ctor_get(v_r_2289_, 2);
lean_dec(v_unused_2776_);
v_unused_2777_ = lean_ctor_get(v_r_2289_, 1);
lean_dec(v_unused_2777_);
v_unused_2778_ = lean_ctor_get(v_r_2289_, 0);
lean_dec(v_unused_2778_);
v___x_2622_ = v_r_2289_;
v_isShared_2623_ = v_isSharedCheck_2773_;
goto v_resetjp_2621_;
}
else
{
lean_dec(v_r_2289_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2773_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v_tree_2625_; 
v___x_2624_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2474_, v_v_2475_, v_l_2476_, v_r_2477_);
v_tree_2625_ = lean_ctor_get(v___x_2624_, 2);
lean_inc(v_tree_2625_);
if (lean_obj_tag(v_tree_2625_) == 0)
{
lean_object* v_k_2626_; lean_object* v_v_2627_; lean_object* v_size_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v_k_2626_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_k_2626_);
v_v_2627_ = lean_ctor_get(v___x_2624_, 1);
lean_inc(v_v_2627_);
lean_dec_ref(v___x_2624_);
v_size_2628_ = lean_ctor_get(v_tree_2625_, 0);
v___x_2629_ = lean_unsigned_to_nat(3u);
v___x_2630_ = lean_nat_mul(v___x_2629_, v_size_2628_);
v___x_2631_ = lean_nat_dec_lt(v___x_2630_, v_size_2468_);
lean_dec(v___x_2630_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
lean_dec(v_r_2472_);
v___x_2632_ = lean_nat_add(v___x_2478_, v_size_2468_);
v___x_2633_ = lean_nat_add(v___x_2632_, v_size_2628_);
lean_dec(v___x_2632_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v_tree_2625_);
lean_ctor_set(v___x_2622_, 3, v_l_2288_);
lean_ctor_set(v___x_2622_, 2, v_v_2627_);
lean_ctor_set(v___x_2622_, 1, v_k_2626_);
lean_ctor_set(v___x_2622_, 0, v___x_2633_);
v___x_2635_ = v___x_2622_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_k_2626_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_v_2627_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_l_2288_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_tree_2625_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
else
{
lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2702_; 
lean_inc(v_l_2471_);
lean_inc(v_v_2470_);
lean_inc(v_k_2469_);
lean_inc(v_size_2468_);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_l_2288_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; lean_object* v_unused_2704_; lean_object* v_unused_2705_; lean_object* v_unused_2706_; lean_object* v_unused_2707_; 
v_unused_2703_ = lean_ctor_get(v_l_2288_, 4);
lean_dec(v_unused_2703_);
v_unused_2704_ = lean_ctor_get(v_l_2288_, 3);
lean_dec(v_unused_2704_);
v_unused_2705_ = lean_ctor_get(v_l_2288_, 2);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_l_2288_, 1);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_l_2288_, 0);
lean_dec(v_unused_2707_);
v___x_2638_ = v_l_2288_;
v_isShared_2639_ = v_isSharedCheck_2702_;
goto v_resetjp_2637_;
}
else
{
lean_dec(v_l_2288_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2702_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v_size_2640_; lean_object* v_size_2641_; lean_object* v_k_2642_; lean_object* v_v_2643_; lean_object* v_l_2644_; lean_object* v_r_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v_size_2640_ = lean_ctor_get(v_l_2471_, 0);
v_size_2641_ = lean_ctor_get(v_r_2472_, 0);
v_k_2642_ = lean_ctor_get(v_r_2472_, 1);
v_v_2643_ = lean_ctor_get(v_r_2472_, 2);
v_l_2644_ = lean_ctor_get(v_r_2472_, 3);
v_r_2645_ = lean_ctor_get(v_r_2472_, 4);
v___x_2646_ = lean_unsigned_to_nat(2u);
v___x_2647_ = lean_nat_mul(v___x_2646_, v_size_2640_);
v___x_2648_ = lean_nat_dec_lt(v_size_2641_, v___x_2647_);
lean_dec(v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2686_; 
lean_inc(v_r_2645_);
lean_inc(v_l_2644_);
lean_inc(v_v_2643_);
lean_inc(v_k_2642_);
lean_del_object(v___x_2638_);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_r_2472_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; lean_object* v_unused_2688_; lean_object* v_unused_2689_; lean_object* v_unused_2690_; lean_object* v_unused_2691_; 
v_unused_2687_ = lean_ctor_get(v_r_2472_, 4);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_r_2472_, 3);
lean_dec(v_unused_2688_);
v_unused_2689_ = lean_ctor_get(v_r_2472_, 2);
lean_dec(v_unused_2689_);
v_unused_2690_ = lean_ctor_get(v_r_2472_, 1);
lean_dec(v_unused_2690_);
v_unused_2691_ = lean_ctor_get(v_r_2472_, 0);
lean_dec(v_unused_2691_);
v___x_2650_ = v_r_2472_;
v_isShared_2651_ = v_isSharedCheck_2686_;
goto v_resetjp_2649_;
}
else
{
lean_dec(v_r_2472_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2686_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___x_2674_; lean_object* v___y_2676_; 
v___x_2652_ = lean_nat_add(v___x_2478_, v_size_2468_);
lean_dec(v_size_2468_);
v___x_2653_ = lean_nat_add(v___x_2652_, v_size_2628_);
lean_dec(v___x_2652_);
v___x_2674_ = lean_nat_add(v___x_2478_, v_size_2640_);
if (lean_obj_tag(v_l_2644_) == 0)
{
lean_object* v_size_2684_; 
v_size_2684_ = lean_ctor_get(v_l_2644_, 0);
lean_inc(v_size_2684_);
v___y_2676_ = v_size_2684_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_unsigned_to_nat(0u);
v___y_2676_ = v___x_2685_;
goto v___jp_2675_;
}
v___jp_2654_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = lean_nat_add(v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec(v___y_2656_);
lean_inc_ref(v_tree_2625_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 4, v_tree_2625_);
lean_ctor_set(v___x_2650_, 3, v_r_2645_);
lean_ctor_set(v___x_2650_, 2, v_v_2627_);
lean_ctor_set(v___x_2650_, 1, v_k_2626_);
lean_ctor_set(v___x_2650_, 0, v___x_2658_);
v___x_2660_ = v___x_2650_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_k_2626_);
lean_ctor_set(v_reuseFailAlloc_2673_, 2, v_v_2627_);
lean_ctor_set(v_reuseFailAlloc_2673_, 3, v_r_2645_);
lean_ctor_set(v_reuseFailAlloc_2673_, 4, v_tree_2625_);
v___x_2660_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
v_isSharedCheck_2667_ = !lean_is_exclusive(v_tree_2625_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; lean_object* v_unused_2669_; lean_object* v_unused_2670_; lean_object* v_unused_2671_; lean_object* v_unused_2672_; 
v_unused_2668_ = lean_ctor_get(v_tree_2625_, 4);
lean_dec(v_unused_2668_);
v_unused_2669_ = lean_ctor_get(v_tree_2625_, 3);
lean_dec(v_unused_2669_);
v_unused_2670_ = lean_ctor_get(v_tree_2625_, 2);
lean_dec(v_unused_2670_);
v_unused_2671_ = lean_ctor_get(v_tree_2625_, 1);
lean_dec(v_unused_2671_);
v_unused_2672_ = lean_ctor_get(v_tree_2625_, 0);
lean_dec(v_unused_2672_);
v___x_2662_ = v_tree_2625_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v_tree_2625_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 4, v___x_2660_);
lean_ctor_set(v___x_2662_, 3, v___y_2655_);
lean_ctor_set(v___x_2662_, 2, v_v_2643_);
lean_ctor_set(v___x_2662_, 1, v_k_2642_);
lean_ctor_set(v___x_2662_, 0, v___x_2653_);
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_k_2642_);
lean_ctor_set(v_reuseFailAlloc_2666_, 2, v_v_2643_);
lean_ctor_set(v_reuseFailAlloc_2666_, 3, v___y_2655_);
lean_ctor_set(v_reuseFailAlloc_2666_, 4, v___x_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
v___jp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2677_ = lean_nat_add(v___x_2674_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec(v___x_2674_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v_l_2644_);
lean_ctor_set(v___x_2622_, 3, v_l_2471_);
lean_ctor_set(v___x_2622_, 2, v_v_2470_);
lean_ctor_set(v___x_2622_, 1, v_k_2469_);
lean_ctor_set(v___x_2622_, 0, v___x_2677_);
v___x_2679_ = v___x_2622_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_k_2469_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_v_2470_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_l_2471_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v_l_2644_);
v___x_2679_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_nat_add(v___x_2478_, v_size_2628_);
if (lean_obj_tag(v_r_2645_) == 0)
{
lean_object* v_size_2681_; 
v_size_2681_ = lean_ctor_get(v_r_2645_, 0);
lean_inc(v_size_2681_);
v___y_2655_ = v___x_2679_;
v___y_2656_ = v___x_2680_;
v___y_2657_ = v_size_2681_;
goto v___jp_2654_;
}
else
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_unsigned_to_nat(0u);
v___y_2655_ = v___x_2679_;
v___y_2656_ = v___x_2680_;
v___y_2657_ = v___x_2682_;
goto v___jp_2654_;
}
}
}
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2692_ = lean_nat_add(v___x_2478_, v_size_2468_);
lean_dec(v_size_2468_);
v___x_2693_ = lean_nat_add(v___x_2692_, v_size_2628_);
lean_dec(v___x_2692_);
v___x_2694_ = lean_nat_add(v___x_2478_, v_size_2628_);
v___x_2695_ = lean_nat_add(v___x_2694_, v_size_2641_);
lean_dec(v___x_2694_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v_tree_2625_);
lean_ctor_set(v___x_2622_, 3, v_r_2472_);
lean_ctor_set(v___x_2622_, 2, v_v_2627_);
lean_ctor_set(v___x_2622_, 1, v_k_2626_);
lean_ctor_set(v___x_2622_, 0, v___x_2695_);
v___x_2697_ = v___x_2622_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_k_2626_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_v_2627_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v_r_2472_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v_tree_2625_);
v___x_2697_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2699_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 4, v___x_2697_);
lean_ctor_set(v___x_2638_, 0, v___x_2693_);
v___x_2699_ = v___x_2638_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_k_2469_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_v_2470_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_l_2471_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2471_) == 0)
{
lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2731_; 
lean_inc_ref(v_l_2471_);
lean_inc(v_v_2470_);
lean_inc(v_k_2469_);
lean_inc(v_size_2468_);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_l_2288_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; lean_object* v_unused_2733_; lean_object* v_unused_2734_; lean_object* v_unused_2735_; lean_object* v_unused_2736_; 
v_unused_2732_ = lean_ctor_get(v_l_2288_, 4);
lean_dec(v_unused_2732_);
v_unused_2733_ = lean_ctor_get(v_l_2288_, 3);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_l_2288_, 2);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_l_2288_, 1);
lean_dec(v_unused_2735_);
v_unused_2736_ = lean_ctor_get(v_l_2288_, 0);
lean_dec(v_unused_2736_);
v___x_2709_ = v_l_2288_;
v_isShared_2710_ = v_isSharedCheck_2731_;
goto v_resetjp_2708_;
}
else
{
lean_dec(v_l_2288_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2731_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
if (lean_obj_tag(v_r_2472_) == 0)
{
lean_object* v_k_2711_; lean_object* v_v_2712_; lean_object* v_size_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v_k_2711_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_k_2711_);
v_v_2712_ = lean_ctor_get(v___x_2624_, 1);
lean_inc(v_v_2712_);
lean_dec_ref(v___x_2624_);
v_size_2713_ = lean_ctor_get(v_r_2472_, 0);
v___x_2714_ = lean_nat_add(v___x_2478_, v_size_2468_);
lean_dec(v_size_2468_);
v___x_2715_ = lean_nat_add(v___x_2478_, v_size_2713_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v_tree_2625_);
lean_ctor_set(v___x_2622_, 3, v_r_2472_);
lean_ctor_set(v___x_2622_, 2, v_v_2712_);
lean_ctor_set(v___x_2622_, 1, v_k_2711_);
lean_ctor_set(v___x_2622_, 0, v___x_2715_);
v___x_2717_ = v___x_2622_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_k_2711_);
lean_ctor_set(v_reuseFailAlloc_2721_, 2, v_v_2712_);
lean_ctor_set(v_reuseFailAlloc_2721_, 3, v_r_2472_);
lean_ctor_set(v_reuseFailAlloc_2721_, 4, v_tree_2625_);
v___x_2717_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2719_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 4, v___x_2717_);
lean_ctor_set(v___x_2709_, 0, v___x_2714_);
v___x_2719_ = v___x_2709_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2714_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_k_2469_);
lean_ctor_set(v_reuseFailAlloc_2720_, 2, v_v_2470_);
lean_ctor_set(v_reuseFailAlloc_2720_, 3, v_l_2471_);
lean_ctor_set(v_reuseFailAlloc_2720_, 4, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
else
{
lean_object* v_k_2722_; lean_object* v_v_2723_; lean_object* v___x_2724_; lean_object* v___x_2726_; 
lean_dec(v_size_2468_);
v_k_2722_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_k_2722_);
v_v_2723_ = lean_ctor_get(v___x_2624_, 1);
lean_inc(v_v_2723_);
lean_dec_ref(v___x_2624_);
v___x_2724_ = lean_unsigned_to_nat(3u);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v_r_2472_);
lean_ctor_set(v___x_2622_, 3, v_r_2472_);
lean_ctor_set(v___x_2622_, 2, v_v_2723_);
lean_ctor_set(v___x_2622_, 1, v_k_2722_);
lean_ctor_set(v___x_2622_, 0, v___x_2478_);
v___x_2726_ = v___x_2622_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_k_2722_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_v_2723_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_r_2472_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v_r_2472_);
v___x_2726_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2728_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 4, v___x_2726_);
lean_ctor_set(v___x_2709_, 0, v___x_2724_);
v___x_2728_ = v___x_2709_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_k_2469_);
lean_ctor_set(v_reuseFailAlloc_2729_, 2, v_v_2470_);
lean_ctor_set(v_reuseFailAlloc_2729_, 3, v_l_2471_);
lean_ctor_set(v_reuseFailAlloc_2729_, 4, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2472_) == 0)
{
lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2761_; 
lean_inc(v_l_2471_);
lean_inc(v_v_2470_);
lean_inc(v_k_2469_);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_l_2288_);
if (v_isSharedCheck_2761_ == 0)
{
lean_object* v_unused_2762_; lean_object* v_unused_2763_; lean_object* v_unused_2764_; lean_object* v_unused_2765_; lean_object* v_unused_2766_; 
v_unused_2762_ = lean_ctor_get(v_l_2288_, 4);
lean_dec(v_unused_2762_);
v_unused_2763_ = lean_ctor_get(v_l_2288_, 3);
lean_dec(v_unused_2763_);
v_unused_2764_ = lean_ctor_get(v_l_2288_, 2);
lean_dec(v_unused_2764_);
v_unused_2765_ = lean_ctor_get(v_l_2288_, 1);
lean_dec(v_unused_2765_);
v_unused_2766_ = lean_ctor_get(v_l_2288_, 0);
lean_dec(v_unused_2766_);
v___x_2738_ = v_l_2288_;
v_isShared_2739_ = v_isSharedCheck_2761_;
goto v_resetjp_2737_;
}
else
{
lean_dec(v_l_2288_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2761_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v_k_2740_; lean_object* v_v_2741_; lean_object* v_k_2742_; lean_object* v_v_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2757_; 
v_k_2740_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_k_2740_);
v_v_2741_ = lean_ctor_get(v___x_2624_, 1);
lean_inc(v_v_2741_);
lean_dec_ref(v___x_2624_);
v_k_2742_ = lean_ctor_get(v_r_2472_, 1);
v_v_2743_ = lean_ctor_get(v_r_2472_, 2);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_r_2472_);
if (v_isSharedCheck_2757_ == 0)
{
lean_object* v_unused_2758_; lean_object* v_unused_2759_; lean_object* v_unused_2760_; 
v_unused_2758_ = lean_ctor_get(v_r_2472_, 4);
lean_dec(v_unused_2758_);
v_unused_2759_ = lean_ctor_get(v_r_2472_, 3);
lean_dec(v_unused_2759_);
v_unused_2760_ = lean_ctor_get(v_r_2472_, 0);
lean_dec(v_unused_2760_);
v___x_2745_ = v_r_2472_;
v_isShared_2746_ = v_isSharedCheck_2757_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_v_2743_);
lean_inc(v_k_2742_);
lean_dec(v_r_2472_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2757_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2747_ = lean_unsigned_to_nat(3u);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v_l_2471_);
lean_ctor_set(v___x_2745_, 3, v_l_2471_);
lean_ctor_set(v___x_2745_, 2, v_v_2470_);
lean_ctor_set(v___x_2745_, 1, v_k_2469_);
lean_ctor_set(v___x_2745_, 0, v___x_2478_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_k_2469_);
lean_ctor_set(v_reuseFailAlloc_2756_, 2, v_v_2470_);
lean_ctor_set(v_reuseFailAlloc_2756_, 3, v_l_2471_);
lean_ctor_set(v_reuseFailAlloc_2756_, 4, v_l_2471_);
v___x_2749_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2751_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v_l_2471_);
lean_ctor_set(v___x_2622_, 3, v_l_2471_);
lean_ctor_set(v___x_2622_, 2, v_v_2741_);
lean_ctor_set(v___x_2622_, 1, v_k_2740_);
lean_ctor_set(v___x_2622_, 0, v___x_2478_);
v___x_2751_ = v___x_2622_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2755_, 3, v_l_2471_);
lean_ctor_set(v_reuseFailAlloc_2755_, 4, v_l_2471_);
v___x_2751_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2753_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 4, v___x_2751_);
lean_ctor_set(v___x_2738_, 3, v___x_2749_);
lean_ctor_set(v___x_2738_, 2, v_v_2743_);
lean_ctor_set(v___x_2738_, 1, v_k_2742_);
lean_ctor_set(v___x_2738_, 0, v___x_2747_);
v___x_2753_ = v___x_2738_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2754_, 3, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2754_, 4, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
}
else
{
lean_object* v_k_2767_; lean_object* v_v_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v_k_2767_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_k_2767_);
v_v_2768_ = lean_ctor_get(v___x_2624_, 1);
lean_inc(v_v_2768_);
lean_dec_ref(v___x_2624_);
v___x_2769_ = lean_unsigned_to_nat(2u);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v_r_2472_);
lean_ctor_set(v___x_2622_, 3, v_l_2288_);
lean_ctor_set(v___x_2622_, 2, v_v_2768_);
lean_ctor_set(v___x_2622_, 1, v_k_2767_);
lean_ctor_set(v___x_2622_, 0, v___x_2769_);
v___x_2771_ = v___x_2622_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_k_2767_);
lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_v_2768_);
lean_ctor_set(v_reuseFailAlloc_2772_, 3, v_l_2288_);
lean_ctor_set(v_reuseFailAlloc_2772_, 4, v_r_2472_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
}
}
else
{
return v_l_2288_;
}
}
else
{
return v_r_2289_;
}
}
default: 
{
lean_object* v_impl_2779_; lean_object* v___x_2780_; 
v_impl_2779_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2284_, v_r_2289_);
v___x_2780_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2779_) == 0)
{
if (lean_obj_tag(v_l_2288_) == 0)
{
lean_object* v_size_2781_; lean_object* v_size_2782_; lean_object* v_k_2783_; lean_object* v_v_2784_; lean_object* v_l_2785_; lean_object* v_r_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v_size_2781_ = lean_ctor_get(v_impl_2779_, 0);
v_size_2782_ = lean_ctor_get(v_l_2288_, 0);
v_k_2783_ = lean_ctor_get(v_l_2288_, 1);
v_v_2784_ = lean_ctor_get(v_l_2288_, 2);
v_l_2785_ = lean_ctor_get(v_l_2288_, 3);
v_r_2786_ = lean_ctor_get(v_l_2288_, 4);
lean_inc(v_r_2786_);
v___x_2787_ = lean_unsigned_to_nat(3u);
v___x_2788_ = lean_nat_mul(v___x_2787_, v_size_2781_);
v___x_2789_ = lean_nat_dec_lt(v___x_2788_, v_size_2782_);
lean_dec(v___x_2788_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
lean_dec(v_r_2786_);
v___x_2790_ = lean_nat_add(v___x_2780_, v_size_2782_);
v___x_2791_ = lean_nat_add(v___x_2790_, v_size_2781_);
lean_dec(v___x_2790_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v_impl_2779_);
lean_ctor_set(v___x_2291_, 0, v___x_2791_);
v___x_2793_ = v___x_2291_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2794_, 3, v_l_2288_);
lean_ctor_set(v_reuseFailAlloc_2794_, 4, v_impl_2779_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
else
{
lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2860_; 
lean_inc(v_l_2785_);
lean_inc(v_v_2784_);
lean_inc(v_k_2783_);
lean_inc(v_size_2782_);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_l_2288_);
if (v_isSharedCheck_2860_ == 0)
{
lean_object* v_unused_2861_; lean_object* v_unused_2862_; lean_object* v_unused_2863_; lean_object* v_unused_2864_; lean_object* v_unused_2865_; 
v_unused_2861_ = lean_ctor_get(v_l_2288_, 4);
lean_dec(v_unused_2861_);
v_unused_2862_ = lean_ctor_get(v_l_2288_, 3);
lean_dec(v_unused_2862_);
v_unused_2863_ = lean_ctor_get(v_l_2288_, 2);
lean_dec(v_unused_2863_);
v_unused_2864_ = lean_ctor_get(v_l_2288_, 1);
lean_dec(v_unused_2864_);
v_unused_2865_ = lean_ctor_get(v_l_2288_, 0);
lean_dec(v_unused_2865_);
v___x_2796_ = v_l_2288_;
v_isShared_2797_ = v_isSharedCheck_2860_;
goto v_resetjp_2795_;
}
else
{
lean_dec(v_l_2288_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2860_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v_size_2798_; lean_object* v_size_2799_; lean_object* v_k_2800_; lean_object* v_v_2801_; lean_object* v_l_2802_; lean_object* v_r_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v_size_2798_ = lean_ctor_get(v_l_2785_, 0);
v_size_2799_ = lean_ctor_get(v_r_2786_, 0);
v_k_2800_ = lean_ctor_get(v_r_2786_, 1);
v_v_2801_ = lean_ctor_get(v_r_2786_, 2);
v_l_2802_ = lean_ctor_get(v_r_2786_, 3);
v_r_2803_ = lean_ctor_get(v_r_2786_, 4);
v___x_2804_ = lean_unsigned_to_nat(2u);
v___x_2805_ = lean_nat_mul(v___x_2804_, v_size_2798_);
v___x_2806_ = lean_nat_dec_lt(v_size_2799_, v___x_2805_);
lean_dec(v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2835_; 
lean_inc(v_r_2803_);
lean_inc(v_l_2802_);
lean_inc(v_v_2801_);
lean_inc(v_k_2800_);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_r_2786_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; lean_object* v_unused_2837_; lean_object* v_unused_2838_; lean_object* v_unused_2839_; lean_object* v_unused_2840_; 
v_unused_2836_ = lean_ctor_get(v_r_2786_, 4);
lean_dec(v_unused_2836_);
v_unused_2837_ = lean_ctor_get(v_r_2786_, 3);
lean_dec(v_unused_2837_);
v_unused_2838_ = lean_ctor_get(v_r_2786_, 2);
lean_dec(v_unused_2838_);
v_unused_2839_ = lean_ctor_get(v_r_2786_, 1);
lean_dec(v_unused_2839_);
v_unused_2840_ = lean_ctor_get(v_r_2786_, 0);
lean_dec(v_unused_2840_);
v___x_2808_ = v_r_2786_;
v_isShared_2809_ = v_isSharedCheck_2835_;
goto v_resetjp_2807_;
}
else
{
lean_dec(v_r_2786_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2835_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___x_2823_; lean_object* v___y_2825_; 
v___x_2810_ = lean_nat_add(v___x_2780_, v_size_2782_);
lean_dec(v_size_2782_);
v___x_2811_ = lean_nat_add(v___x_2810_, v_size_2781_);
lean_dec(v___x_2810_);
v___x_2823_ = lean_nat_add(v___x_2780_, v_size_2798_);
if (lean_obj_tag(v_l_2802_) == 0)
{
lean_object* v_size_2833_; 
v_size_2833_ = lean_ctor_get(v_l_2802_, 0);
lean_inc(v_size_2833_);
v___y_2825_ = v_size_2833_;
goto v___jp_2824_;
}
else
{
lean_object* v___x_2834_; 
v___x_2834_ = lean_unsigned_to_nat(0u);
v___y_2825_ = v___x_2834_;
goto v___jp_2824_;
}
v___jp_2812_:
{
lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2816_ = lean_nat_add(v___y_2813_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec(v___y_2813_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 4, v_impl_2779_);
lean_ctor_set(v___x_2808_, 3, v_r_2803_);
lean_ctor_set(v___x_2808_, 2, v_v_2287_);
lean_ctor_set(v___x_2808_, 1, v_k_2286_);
lean_ctor_set(v___x_2808_, 0, v___x_2816_);
v___x_2818_ = v___x_2808_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_r_2803_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_impl_2779_);
v___x_2818_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 4, v___x_2818_);
lean_ctor_set(v___x_2796_, 3, v___y_2814_);
lean_ctor_set(v___x_2796_, 2, v_v_2801_);
lean_ctor_set(v___x_2796_, 1, v_k_2800_);
lean_ctor_set(v___x_2796_, 0, v___x_2811_);
v___x_2820_ = v___x_2796_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_k_2800_);
lean_ctor_set(v_reuseFailAlloc_2821_, 2, v_v_2801_);
lean_ctor_set(v_reuseFailAlloc_2821_, 3, v___y_2814_);
lean_ctor_set(v_reuseFailAlloc_2821_, 4, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
v___jp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2828_; 
v___x_2826_ = lean_nat_add(v___x_2823_, v___y_2825_);
lean_dec(v___y_2825_);
lean_dec(v___x_2823_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v_l_2802_);
lean_ctor_set(v___x_2291_, 3, v_l_2785_);
lean_ctor_set(v___x_2291_, 2, v_v_2784_);
lean_ctor_set(v___x_2291_, 1, v_k_2783_);
lean_ctor_set(v___x_2291_, 0, v___x_2826_);
v___x_2828_ = v___x_2291_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_k_2783_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_v_2784_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_l_2785_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_l_2802_);
v___x_2828_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_nat_add(v___x_2780_, v_size_2781_);
if (lean_obj_tag(v_r_2803_) == 0)
{
lean_object* v_size_2830_; 
v_size_2830_ = lean_ctor_get(v_r_2803_, 0);
lean_inc(v_size_2830_);
v___y_2813_ = v___x_2829_;
v___y_2814_ = v___x_2828_;
v___y_2815_ = v_size_2830_;
goto v___jp_2812_;
}
else
{
lean_object* v___x_2831_; 
v___x_2831_ = lean_unsigned_to_nat(0u);
v___y_2813_ = v___x_2829_;
v___y_2814_ = v___x_2828_;
v___y_2815_ = v___x_2831_;
goto v___jp_2812_;
}
}
}
}
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
lean_del_object(v___x_2291_);
v___x_2841_ = lean_nat_add(v___x_2780_, v_size_2782_);
lean_dec(v_size_2782_);
v___x_2842_ = lean_nat_add(v___x_2841_, v_size_2781_);
lean_dec(v___x_2841_);
v___x_2843_ = lean_nat_add(v___x_2780_, v_size_2781_);
v___x_2844_ = lean_nat_add(v___x_2843_, v_size_2799_);
lean_dec(v___x_2843_);
lean_inc_ref(v_impl_2779_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 4, v_impl_2779_);
lean_ctor_set(v___x_2796_, 3, v_r_2786_);
lean_ctor_set(v___x_2796_, 2, v_v_2287_);
lean_ctor_set(v___x_2796_, 1, v_k_2286_);
lean_ctor_set(v___x_2796_, 0, v___x_2844_);
v___x_2846_ = v___x_2796_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2844_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2859_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2859_, 3, v_r_2786_);
lean_ctor_set(v_reuseFailAlloc_2859_, 4, v_impl_2779_);
v___x_2846_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
v_isSharedCheck_2853_ = !lean_is_exclusive(v_impl_2779_);
if (v_isSharedCheck_2853_ == 0)
{
lean_object* v_unused_2854_; lean_object* v_unused_2855_; lean_object* v_unused_2856_; lean_object* v_unused_2857_; lean_object* v_unused_2858_; 
v_unused_2854_ = lean_ctor_get(v_impl_2779_, 4);
lean_dec(v_unused_2854_);
v_unused_2855_ = lean_ctor_get(v_impl_2779_, 3);
lean_dec(v_unused_2855_);
v_unused_2856_ = lean_ctor_get(v_impl_2779_, 2);
lean_dec(v_unused_2856_);
v_unused_2857_ = lean_ctor_get(v_impl_2779_, 1);
lean_dec(v_unused_2857_);
v_unused_2858_ = lean_ctor_get(v_impl_2779_, 0);
lean_dec(v_unused_2858_);
v___x_2848_ = v_impl_2779_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_dec(v_impl_2779_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 4, v___x_2846_);
lean_ctor_set(v___x_2848_, 3, v_l_2785_);
lean_ctor_set(v___x_2848_, 2, v_v_2784_);
lean_ctor_set(v___x_2848_, 1, v_k_2783_);
lean_ctor_set(v___x_2848_, 0, v___x_2842_);
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_k_2783_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v_v_2784_);
lean_ctor_set(v_reuseFailAlloc_2852_, 3, v_l_2785_);
lean_ctor_set(v_reuseFailAlloc_2852_, 4, v___x_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
v_size_2866_ = lean_ctor_get(v_impl_2779_, 0);
v___x_2867_ = lean_nat_add(v___x_2780_, v_size_2866_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v_impl_2779_);
lean_ctor_set(v___x_2291_, 0, v___x_2867_);
v___x_2869_ = v___x_2291_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_l_2288_);
lean_ctor_set(v_reuseFailAlloc_2870_, 4, v_impl_2779_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
else
{
if (lean_obj_tag(v_l_2288_) == 0)
{
lean_object* v_l_2871_; 
v_l_2871_ = lean_ctor_get(v_l_2288_, 3);
if (lean_obj_tag(v_l_2871_) == 0)
{
lean_object* v_r_2872_; 
lean_inc_ref(v_l_2871_);
v_r_2872_ = lean_ctor_get(v_l_2288_, 4);
lean_inc(v_r_2872_);
if (lean_obj_tag(v_r_2872_) == 0)
{
lean_object* v_size_2873_; lean_object* v_k_2874_; lean_object* v_v_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2888_; 
v_size_2873_ = lean_ctor_get(v_l_2288_, 0);
v_k_2874_ = lean_ctor_get(v_l_2288_, 1);
v_v_2875_ = lean_ctor_get(v_l_2288_, 2);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_l_2288_);
if (v_isSharedCheck_2888_ == 0)
{
lean_object* v_unused_2889_; lean_object* v_unused_2890_; 
v_unused_2889_ = lean_ctor_get(v_l_2288_, 4);
lean_dec(v_unused_2889_);
v_unused_2890_ = lean_ctor_get(v_l_2288_, 3);
lean_dec(v_unused_2890_);
v___x_2877_ = v_l_2288_;
v_isShared_2878_ = v_isSharedCheck_2888_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_v_2875_);
lean_inc(v_k_2874_);
lean_inc(v_size_2873_);
lean_dec(v_l_2288_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2888_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v_size_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v_size_2879_ = lean_ctor_get(v_r_2872_, 0);
v___x_2880_ = lean_nat_add(v___x_2780_, v_size_2873_);
lean_dec(v_size_2873_);
v___x_2881_ = lean_nat_add(v___x_2780_, v_size_2879_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 4, v_impl_2779_);
lean_ctor_set(v___x_2877_, 3, v_r_2872_);
lean_ctor_set(v___x_2877_, 2, v_v_2287_);
lean_ctor_set(v___x_2877_, 1, v_k_2286_);
lean_ctor_set(v___x_2877_, 0, v___x_2881_);
v___x_2883_ = v___x_2877_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_r_2872_);
lean_ctor_set(v_reuseFailAlloc_2887_, 4, v_impl_2779_);
v___x_2883_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2885_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v___x_2883_);
lean_ctor_set(v___x_2291_, 3, v_l_2871_);
lean_ctor_set(v___x_2291_, 2, v_v_2875_);
lean_ctor_set(v___x_2291_, 1, v_k_2874_);
lean_ctor_set(v___x_2291_, 0, v___x_2880_);
v___x_2885_ = v___x_2291_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2880_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_k_2874_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_v_2875_);
lean_ctor_set(v_reuseFailAlloc_2886_, 3, v_l_2871_);
lean_ctor_set(v_reuseFailAlloc_2886_, 4, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_k_2891_; lean_object* v_v_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2903_; 
v_k_2891_ = lean_ctor_get(v_l_2288_, 1);
v_v_2892_ = lean_ctor_get(v_l_2288_, 2);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_l_2288_);
if (v_isSharedCheck_2903_ == 0)
{
lean_object* v_unused_2904_; lean_object* v_unused_2905_; lean_object* v_unused_2906_; 
v_unused_2904_ = lean_ctor_get(v_l_2288_, 4);
lean_dec(v_unused_2904_);
v_unused_2905_ = lean_ctor_get(v_l_2288_, 3);
lean_dec(v_unused_2905_);
v_unused_2906_ = lean_ctor_get(v_l_2288_, 0);
lean_dec(v_unused_2906_);
v___x_2894_ = v_l_2288_;
v_isShared_2895_ = v_isSharedCheck_2903_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_v_2892_);
lean_inc(v_k_2891_);
lean_dec(v_l_2288_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2903_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2896_ = lean_unsigned_to_nat(3u);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 3, v_r_2872_);
lean_ctor_set(v___x_2894_, 2, v_v_2287_);
lean_ctor_set(v___x_2894_, 1, v_k_2286_);
lean_ctor_set(v___x_2894_, 0, v___x_2780_);
v___x_2898_ = v___x_2894_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2902_, 3, v_r_2872_);
lean_ctor_set(v_reuseFailAlloc_2902_, 4, v_r_2872_);
v___x_2898_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2900_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v___x_2898_);
lean_ctor_set(v___x_2291_, 3, v_l_2871_);
lean_ctor_set(v___x_2291_, 2, v_v_2892_);
lean_ctor_set(v___x_2291_, 1, v_k_2891_);
lean_ctor_set(v___x_2291_, 0, v___x_2896_);
v___x_2900_ = v___x_2291_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_k_2891_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_v_2892_);
lean_ctor_set(v_reuseFailAlloc_2901_, 3, v_l_2871_);
lean_ctor_set(v_reuseFailAlloc_2901_, 4, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
else
{
lean_object* v_r_2907_; 
v_r_2907_ = lean_ctor_get(v_l_2288_, 4);
lean_inc(v_r_2907_);
if (lean_obj_tag(v_r_2907_) == 0)
{
lean_object* v_k_2908_; lean_object* v_v_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2932_; 
lean_inc(v_l_2871_);
v_k_2908_ = lean_ctor_get(v_l_2288_, 1);
v_v_2909_ = lean_ctor_get(v_l_2288_, 2);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_l_2288_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; lean_object* v_unused_2934_; lean_object* v_unused_2935_; 
v_unused_2933_ = lean_ctor_get(v_l_2288_, 4);
lean_dec(v_unused_2933_);
v_unused_2934_ = lean_ctor_get(v_l_2288_, 3);
lean_dec(v_unused_2934_);
v_unused_2935_ = lean_ctor_get(v_l_2288_, 0);
lean_dec(v_unused_2935_);
v___x_2911_ = v_l_2288_;
v_isShared_2912_ = v_isSharedCheck_2932_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_v_2909_);
lean_inc(v_k_2908_);
lean_dec(v_l_2288_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2932_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v_k_2913_; lean_object* v_v_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2928_; 
v_k_2913_ = lean_ctor_get(v_r_2907_, 1);
v_v_2914_ = lean_ctor_get(v_r_2907_, 2);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_r_2907_);
if (v_isSharedCheck_2928_ == 0)
{
lean_object* v_unused_2929_; lean_object* v_unused_2930_; lean_object* v_unused_2931_; 
v_unused_2929_ = lean_ctor_get(v_r_2907_, 4);
lean_dec(v_unused_2929_);
v_unused_2930_ = lean_ctor_get(v_r_2907_, 3);
lean_dec(v_unused_2930_);
v_unused_2931_ = lean_ctor_get(v_r_2907_, 0);
lean_dec(v_unused_2931_);
v___x_2916_ = v_r_2907_;
v_isShared_2917_ = v_isSharedCheck_2928_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_v_2914_);
lean_inc(v_k_2913_);
lean_dec(v_r_2907_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2928_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2918_ = lean_unsigned_to_nat(3u);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 4, v_l_2871_);
lean_ctor_set(v___x_2916_, 3, v_l_2871_);
lean_ctor_set(v___x_2916_, 2, v_v_2909_);
lean_ctor_set(v___x_2916_, 1, v_k_2908_);
lean_ctor_set(v___x_2916_, 0, v___x_2780_);
v___x_2920_ = v___x_2916_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_k_2908_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_v_2909_);
lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_l_2871_);
lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_l_2871_);
v___x_2920_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2922_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 4, v_l_2871_);
lean_ctor_set(v___x_2911_, 2, v_v_2287_);
lean_ctor_set(v___x_2911_, 1, v_k_2286_);
lean_ctor_set(v___x_2911_, 0, v___x_2780_);
v___x_2922_ = v___x_2911_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2926_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2926_, 3, v_l_2871_);
lean_ctor_set(v_reuseFailAlloc_2926_, 4, v_l_2871_);
v___x_2922_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2924_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v___x_2922_);
lean_ctor_set(v___x_2291_, 3, v___x_2920_);
lean_ctor_set(v___x_2291_, 2, v_v_2914_);
lean_ctor_set(v___x_2291_, 1, v_k_2913_);
lean_ctor_set(v___x_2291_, 0, v___x_2918_);
v___x_2924_ = v___x_2291_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_k_2913_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_v_2914_);
lean_ctor_set(v_reuseFailAlloc_2925_, 3, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_2925_, 4, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = lean_unsigned_to_nat(2u);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v_r_2907_);
lean_ctor_set(v___x_2291_, 0, v___x_2936_);
v___x_2938_ = v___x_2291_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v_l_2288_);
lean_ctor_set(v_reuseFailAlloc_2939_, 4, v_r_2907_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
else
{
lean_object* v___x_2941_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v_l_2288_);
lean_ctor_set(v___x_2291_, 0, v___x_2780_);
v___x_2941_ = v___x_2291_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2942_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2942_, 3, v_l_2288_);
lean_ctor_set(v_reuseFailAlloc_2942_, 4, v_l_2288_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
}
}
else
{
return v_t_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_2945_, lean_object* v_t_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2945_, v_t_2946_);
lean_dec(v_k_2945_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_2948_, lean_object* v_declName_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_ext_2955_; lean_object* v_toEnvExtension_2956_; lean_object* v_env_2957_; lean_object* v_asyncMode_2958_; uint8_t v___x_2959_; lean_object* v___x_2960_; lean_object* v_funCC_2961_; lean_object* v___y_2963_; uint8_t v___x_2989_; 
v___x_2953_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2954_ = lean_st_ref_get(v_a_2951_);
v_ext_2955_ = lean_ctor_get(v_ext_2948_, 1);
v_toEnvExtension_2956_ = lean_ctor_get(v_ext_2955_, 0);
v_env_2957_ = lean_ctor_get(v___x_2954_, 0);
lean_inc_ref(v_env_2957_);
lean_dec(v___x_2954_);
v_asyncMode_2958_ = lean_ctor_get(v_toEnvExtension_2956_, 2);
v___x_2959_ = 0;
v___x_2960_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2953_, v_ext_2948_, v_env_2957_, v_asyncMode_2958_, v___x_2959_);
v_funCC_2961_ = lean_ctor_get(v___x_2960_, 2);
lean_inc(v_funCC_2961_);
lean_dec(v___x_2960_);
v___x_2989_ = l_Lean_NameSet_contains(v_funCC_2961_, v_declName_2949_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
lean_inc(v_declName_2949_);
v___x_2990_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2949_, v_a_2950_, v_a_2951_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_dec_ref_known(v___x_2990_, 1);
v___y_2963_ = v_a_2951_;
goto v___jp_2962_;
}
else
{
lean_dec(v_funCC_2961_);
lean_dec(v_declName_2949_);
lean_dec_ref(v_ext_2948_);
return v___x_2990_;
}
}
else
{
v___y_2963_ = v_a_2951_;
goto v___jp_2962_;
}
v___jp_2962_:
{
lean_object* v___x_2964_; lean_object* v___f_2965_; lean_object* v___x_2966_; lean_object* v_env_2967_; lean_object* v_nextMacroScope_2968_; lean_object* v_ngen_2969_; lean_object* v_auxDeclNGen_2970_; lean_object* v_traceState_2971_; lean_object* v_recordedDeps_2972_; lean_object* v_messages_2973_; lean_object* v_infoState_2974_; lean_object* v_snapshotTasks_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2987_; 
v___x_2964_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_2949_, v_funCC_2961_);
lean_dec(v_declName_2949_);
v___f_2965_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_2965_, 0, v___x_2964_);
v___x_2966_ = lean_st_ref_take(v___y_2963_);
v_env_2967_ = lean_ctor_get(v___x_2966_, 0);
v_nextMacroScope_2968_ = lean_ctor_get(v___x_2966_, 1);
v_ngen_2969_ = lean_ctor_get(v___x_2966_, 2);
v_auxDeclNGen_2970_ = lean_ctor_get(v___x_2966_, 3);
v_traceState_2971_ = lean_ctor_get(v___x_2966_, 4);
v_recordedDeps_2972_ = lean_ctor_get(v___x_2966_, 6);
v_messages_2973_ = lean_ctor_get(v___x_2966_, 7);
v_infoState_2974_ = lean_ctor_get(v___x_2966_, 8);
v_snapshotTasks_2975_ = lean_ctor_get(v___x_2966_, 9);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2966_, 5);
lean_dec(v_unused_2988_);
v___x_2977_ = v___x_2966_;
v_isShared_2978_ = v_isSharedCheck_2987_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_snapshotTasks_2975_);
lean_inc(v_infoState_2974_);
lean_inc(v_messages_2973_);
lean_inc(v_recordedDeps_2972_);
lean_inc(v_traceState_2971_);
lean_inc(v_auxDeclNGen_2970_);
lean_inc(v_ngen_2969_);
lean_inc(v_nextMacroScope_2968_);
lean_inc(v_env_2967_);
lean_dec(v___x_2966_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2987_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2979_ = lean_box(0);
v___x_2980_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2948_, v_env_2967_, v___f_2965_);
v___x_2981_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 5, v___x_2981_);
lean_ctor_set(v___x_2977_, 0, v___x_2980_);
v___x_2983_ = v___x_2977_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_nextMacroScope_2968_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_ngen_2969_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_auxDeclNGen_2970_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v_traceState_2971_);
lean_ctor_set(v_reuseFailAlloc_2986_, 5, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_2986_, 6, v_recordedDeps_2972_);
lean_ctor_set(v_reuseFailAlloc_2986_, 7, v_messages_2973_);
lean_ctor_set(v_reuseFailAlloc_2986_, 8, v_infoState_2974_);
lean_ctor_set(v_reuseFailAlloc_2986_, 9, v_snapshotTasks_2975_);
v___x_2983_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_st_ref_put(v___y_2963_, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2979_);
return v___x_2985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_2991_, lean_object* v_declName_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2991_, v_declName_2992_, v_a_2993_, v_a_2994_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_2997_, lean_object* v_k_2998_, lean_object* v_t_2999_, lean_object* v_h_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2998_, v_t_2999_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_3002_, lean_object* v_k_3003_, lean_object* v_t_3004_, lean_object* v_h_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_3002_, v_k_3003_, v_t_3004_, v_h_3005_);
lean_dec(v_k_3003_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_3007_, lean_object* v_s_3008_){
_start:
{
lean_object* v_casesTypes_3009_; lean_object* v_extThms_3010_; lean_object* v_funCC_3011_; lean_object* v_inj_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
v_casesTypes_3009_ = lean_ctor_get(v_s_3008_, 0);
v_extThms_3010_ = lean_ctor_get(v_s_3008_, 1);
v_funCC_3011_ = lean_ctor_get(v_s_3008_, 2);
v_inj_3012_ = lean_ctor_get(v_s_3008_, 4);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_s_3008_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v_s_3008_, 3);
lean_dec(v_unused_3020_);
v___x_3014_ = v_s_3008_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_inj_3012_);
lean_inc(v_funCC_3011_);
lean_inc(v_extThms_3010_);
lean_inc(v_casesTypes_3009_);
lean_dec(v_s_3008_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 3, v_a_3007_);
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_casesTypes_3009_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_extThms_3010_);
lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_funCC_3011_);
lean_ctor_set(v_reuseFailAlloc_3018_, 3, v_a_3007_);
lean_ctor_set(v_reuseFailAlloc_3018_, 4, v_inj_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_3021_, lean_object* v_declName_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v_ext_3030_; lean_object* v_toEnvExtension_3031_; lean_object* v_env_3032_; lean_object* v_asyncMode_3033_; uint8_t v___x_3034_; lean_object* v___x_3035_; lean_object* v_ematch_3036_; lean_object* v___x_3037_; 
v___x_3028_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3029_ = lean_st_ref_get(v_a_3026_);
v_ext_3030_ = lean_ctor_get(v_ext_3021_, 1);
v_toEnvExtension_3031_ = lean_ctor_get(v_ext_3030_, 0);
v_env_3032_ = lean_ctor_get(v___x_3029_, 0);
lean_inc_ref(v_env_3032_);
lean_dec(v___x_3029_);
v_asyncMode_3033_ = lean_ctor_get(v_toEnvExtension_3031_, 2);
v___x_3034_ = 0;
v___x_3035_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3028_, v_ext_3021_, v_env_3032_, v_asyncMode_3033_, v___x_3034_);
v_ematch_3036_ = lean_ctor_get(v___x_3035_, 3);
lean_inc_ref(v_ematch_3036_);
lean_dec(v___x_3035_);
v___x_3037_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_3036_, v_declName_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3083_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3083_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3083_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___f_3042_; lean_object* v___x_3043_; lean_object* v_env_3044_; lean_object* v_nextMacroScope_3045_; lean_object* v_ngen_3046_; lean_object* v_auxDeclNGen_3047_; lean_object* v_traceState_3048_; lean_object* v_recordedDeps_3049_; lean_object* v_messages_3050_; lean_object* v_infoState_3051_; lean_object* v_snapshotTasks_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3081_; 
v___f_3042_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_3042_, 0, v_a_3038_);
v___x_3043_ = lean_st_ref_take(v_a_3026_);
v_env_3044_ = lean_ctor_get(v___x_3043_, 0);
v_nextMacroScope_3045_ = lean_ctor_get(v___x_3043_, 1);
v_ngen_3046_ = lean_ctor_get(v___x_3043_, 2);
v_auxDeclNGen_3047_ = lean_ctor_get(v___x_3043_, 3);
v_traceState_3048_ = lean_ctor_get(v___x_3043_, 4);
v_recordedDeps_3049_ = lean_ctor_get(v___x_3043_, 6);
v_messages_3050_ = lean_ctor_get(v___x_3043_, 7);
v_infoState_3051_ = lean_ctor_get(v___x_3043_, 8);
v_snapshotTasks_3052_ = lean_ctor_get(v___x_3043_, 9);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v___x_3043_, 5);
lean_dec(v_unused_3082_);
v___x_3054_ = v___x_3043_;
v_isShared_3055_ = v_isSharedCheck_3081_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_snapshotTasks_3052_);
lean_inc(v_infoState_3051_);
lean_inc(v_messages_3050_);
lean_inc(v_recordedDeps_3049_);
lean_inc(v_traceState_3048_);
lean_inc(v_auxDeclNGen_3047_);
lean_inc(v_ngen_3046_);
lean_inc(v_nextMacroScope_3045_);
lean_inc(v_env_3044_);
lean_dec(v___x_3043_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3081_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v___x_3056_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_3021_, v_env_3044_, v___f_3042_);
v___x_3057_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 5, v___x_3057_);
lean_ctor_set(v___x_3054_, 0, v___x_3056_);
v___x_3059_ = v___x_3054_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v_nextMacroScope_3045_);
lean_ctor_set(v_reuseFailAlloc_3080_, 2, v_ngen_3046_);
lean_ctor_set(v_reuseFailAlloc_3080_, 3, v_auxDeclNGen_3047_);
lean_ctor_set(v_reuseFailAlloc_3080_, 4, v_traceState_3048_);
lean_ctor_set(v_reuseFailAlloc_3080_, 5, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3080_, 6, v_recordedDeps_3049_);
lean_ctor_set(v_reuseFailAlloc_3080_, 7, v_messages_3050_);
lean_ctor_set(v_reuseFailAlloc_3080_, 8, v_infoState_3051_);
lean_ctor_set(v_reuseFailAlloc_3080_, 9, v_snapshotTasks_3052_);
v___x_3059_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v_mctx_3062_; lean_object* v_zetaDeltaFVarIds_3063_; lean_object* v_postponed_3064_; lean_object* v_diag_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3078_; 
v___x_3060_ = lean_st_ref_put(v_a_3026_, v___x_3059_);
v___x_3061_ = lean_st_ref_take(v_a_3024_);
v_mctx_3062_ = lean_ctor_get(v___x_3061_, 0);
v_zetaDeltaFVarIds_3063_ = lean_ctor_get(v___x_3061_, 2);
v_postponed_3064_ = lean_ctor_get(v___x_3061_, 3);
v_diag_3065_ = lean_ctor_get(v___x_3061_, 4);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v___x_3061_, 1);
lean_dec(v_unused_3079_);
v___x_3067_ = v___x_3061_;
v_isShared_3068_ = v_isSharedCheck_3078_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_diag_3065_);
lean_inc(v_postponed_3064_);
lean_inc(v_zetaDeltaFVarIds_3063_);
lean_inc(v_mctx_3062_);
lean_dec(v___x_3061_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3078_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3072_; 
v___x_3069_ = lean_box(0);
v___x_3070_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5);
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 1, v___x_3070_);
v___x_3072_ = v___x_3067_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_mctx_3062_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_zetaDeltaFVarIds_3063_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v_postponed_3064_);
lean_ctor_set(v_reuseFailAlloc_3077_, 4, v_diag_3065_);
v___x_3072_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = lean_st_ref_put(v_a_3024_, v___x_3072_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3069_);
v___x_3075_ = v___x_3040_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3069_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v_ext_3021_);
v_a_3084_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3037_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3037_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_3092_, lean_object* v_declName_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_3092_, v_declName_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_3100_, lean_object* v_s_3101_){
_start:
{
lean_object* v_casesTypes_3102_; lean_object* v_extThms_3103_; lean_object* v_funCC_3104_; lean_object* v_ematch_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
v_casesTypes_3102_ = lean_ctor_get(v_s_3101_, 0);
v_extThms_3103_ = lean_ctor_get(v_s_3101_, 1);
v_funCC_3104_ = lean_ctor_get(v_s_3101_, 2);
v_ematch_3105_ = lean_ctor_get(v_s_3101_, 3);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_s_3101_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; 
v_unused_3113_ = lean_ctor_get(v_s_3101_, 4);
lean_dec(v_unused_3113_);
v___x_3107_ = v_s_3101_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_ematch_3105_);
lean_inc(v_funCC_3104_);
lean_inc(v_extThms_3103_);
lean_inc(v_casesTypes_3102_);
lean_dec(v_s_3101_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 4, v_a_3100_);
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_casesTypes_3102_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_extThms_3103_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_funCC_3104_);
lean_ctor_set(v_reuseFailAlloc_3111_, 3, v_ematch_3105_);
lean_ctor_set(v_reuseFailAlloc_3111_, 4, v_a_3100_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_3114_, lean_object* v_declName_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v_ext_3123_; lean_object* v_toEnvExtension_3124_; lean_object* v_env_3125_; lean_object* v_asyncMode_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v_inj_3129_; lean_object* v___x_3130_; 
v___x_3121_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3122_ = lean_st_ref_get(v_a_3119_);
v_ext_3123_ = lean_ctor_get(v_ext_3114_, 1);
v_toEnvExtension_3124_ = lean_ctor_get(v_ext_3123_, 0);
v_env_3125_ = lean_ctor_get(v___x_3122_, 0);
lean_inc_ref(v_env_3125_);
lean_dec(v___x_3122_);
v_asyncMode_3126_ = lean_ctor_get(v_toEnvExtension_3124_, 2);
v___x_3127_ = 0;
v___x_3128_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3121_, v_ext_3114_, v_env_3125_, v_asyncMode_3126_, v___x_3127_);
v_inj_3129_ = lean_ctor_get(v___x_3128_, 4);
lean_inc_ref(v_inj_3129_);
lean_dec(v___x_3128_);
v___x_3130_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_3129_, v_declName_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3176_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3176_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3176_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___f_3135_; lean_object* v___x_3136_; lean_object* v_env_3137_; lean_object* v_nextMacroScope_3138_; lean_object* v_ngen_3139_; lean_object* v_auxDeclNGen_3140_; lean_object* v_traceState_3141_; lean_object* v_recordedDeps_3142_; lean_object* v_messages_3143_; lean_object* v_infoState_3144_; lean_object* v_snapshotTasks_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3174_; 
v___f_3135_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_3135_, 0, v_a_3131_);
v___x_3136_ = lean_st_ref_take(v_a_3119_);
v_env_3137_ = lean_ctor_get(v___x_3136_, 0);
v_nextMacroScope_3138_ = lean_ctor_get(v___x_3136_, 1);
v_ngen_3139_ = lean_ctor_get(v___x_3136_, 2);
v_auxDeclNGen_3140_ = lean_ctor_get(v___x_3136_, 3);
v_traceState_3141_ = lean_ctor_get(v___x_3136_, 4);
v_recordedDeps_3142_ = lean_ctor_get(v___x_3136_, 6);
v_messages_3143_ = lean_ctor_get(v___x_3136_, 7);
v_infoState_3144_ = lean_ctor_get(v___x_3136_, 8);
v_snapshotTasks_3145_ = lean_ctor_get(v___x_3136_, 9);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v___x_3136_, 5);
lean_dec(v_unused_3175_);
v___x_3147_ = v___x_3136_;
v_isShared_3148_ = v_isSharedCheck_3174_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_snapshotTasks_3145_);
lean_inc(v_infoState_3144_);
lean_inc(v_messages_3143_);
lean_inc(v_recordedDeps_3142_);
lean_inc(v_traceState_3141_);
lean_inc(v_auxDeclNGen_3140_);
lean_inc(v_ngen_3139_);
lean_inc(v_nextMacroScope_3138_);
lean_inc(v_env_3137_);
lean_dec(v___x_3136_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3174_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3149_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_3114_, v_env_3137_, v___f_3135_);
v___x_3150_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 5, v___x_3150_);
lean_ctor_set(v___x_3147_, 0, v___x_3149_);
v___x_3152_ = v___x_3147_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3149_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_nextMacroScope_3138_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v_ngen_3139_);
lean_ctor_set(v_reuseFailAlloc_3173_, 3, v_auxDeclNGen_3140_);
lean_ctor_set(v_reuseFailAlloc_3173_, 4, v_traceState_3141_);
lean_ctor_set(v_reuseFailAlloc_3173_, 5, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3173_, 6, v_recordedDeps_3142_);
lean_ctor_set(v_reuseFailAlloc_3173_, 7, v_messages_3143_);
lean_ctor_set(v_reuseFailAlloc_3173_, 8, v_infoState_3144_);
lean_ctor_set(v_reuseFailAlloc_3173_, 9, v_snapshotTasks_3145_);
v___x_3152_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v_mctx_3155_; lean_object* v_zetaDeltaFVarIds_3156_; lean_object* v_postponed_3157_; lean_object* v_diag_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3171_; 
v___x_3153_ = lean_st_ref_put(v_a_3119_, v___x_3152_);
v___x_3154_ = lean_st_ref_take(v_a_3117_);
v_mctx_3155_ = lean_ctor_get(v___x_3154_, 0);
v_zetaDeltaFVarIds_3156_ = lean_ctor_get(v___x_3154_, 2);
v_postponed_3157_ = lean_ctor_get(v___x_3154_, 3);
v_diag_3158_ = lean_ctor_get(v___x_3154_, 4);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v___x_3154_, 1);
lean_dec(v_unused_3172_);
v___x_3160_ = v___x_3154_;
v_isShared_3161_ = v_isSharedCheck_3171_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_diag_3158_);
lean_inc(v_postponed_3157_);
lean_inc(v_zetaDeltaFVarIds_3156_);
lean_inc(v_mctx_3155_);
lean_dec(v___x_3154_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3171_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3162_ = lean_box(0);
v___x_3163_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v___x_3163_);
v___x_3165_ = v___x_3160_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_mctx_3155_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_zetaDeltaFVarIds_3156_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v_postponed_3157_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v_diag_3158_);
v___x_3165_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3166_ = lean_st_ref_put(v_a_3117_, v___x_3165_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3162_);
v___x_3168_ = v___x_3133_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3162_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec_ref(v_ext_3114_);
v_a_3177_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3130_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3130_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_3185_, lean_object* v_declName_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_3185_, v_declName_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
return v_res_3192_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3193_, lean_object* v_i_3194_, lean_object* v_k_3195_){
_start:
{
lean_object* v___x_3196_; uint8_t v___x_3197_; 
v___x_3196_ = lean_array_get_size(v_keys_3193_);
v___x_3197_ = lean_nat_dec_lt(v_i_3194_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_dec(v_i_3194_);
return v___x_3197_;
}
else
{
lean_object* v_k_x27_3198_; uint8_t v___x_3199_; 
v_k_x27_3198_ = lean_array_fget_borrowed(v_keys_3193_, v_i_3194_);
v___x_3199_ = lean_name_eq(v_k_3195_, v_k_x27_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_unsigned_to_nat(1u);
v___x_3201_ = lean_nat_add(v_i_3194_, v___x_3200_);
lean_dec(v_i_3194_);
v_i_3194_ = v___x_3201_;
goto _start;
}
else
{
lean_dec(v_i_3194_);
return v___x_3197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3203_, lean_object* v_i_3204_, lean_object* v_k_3205_){
_start:
{
uint8_t v_res_3206_; lean_object* v_r_3207_; 
v_res_3206_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_3203_, v_i_3204_, v_k_3205_);
lean_dec(v_k_3205_);
lean_dec_ref(v_keys_3203_);
v_r_3207_ = lean_box(v_res_3206_);
return v_r_3207_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_3208_, size_t v_x_3209_, lean_object* v_x_3210_){
_start:
{
if (lean_obj_tag(v_x_3208_) == 0)
{
lean_object* v_es_3211_; lean_object* v___x_3212_; size_t v___x_3213_; size_t v___x_3214_; lean_object* v_j_3215_; lean_object* v___x_3216_; 
v_es_3211_ = lean_ctor_get(v_x_3208_, 0);
v___x_3212_ = lean_box(2);
v___x_3213_ = ((size_t)31ULL);
v___x_3214_ = lean_usize_land(v_x_3209_, v___x_3213_);
v_j_3215_ = lean_usize_to_nat(v___x_3214_);
v___x_3216_ = lean_array_get_borrowed(v___x_3212_, v_es_3211_, v_j_3215_);
lean_dec(v_j_3215_);
switch(lean_obj_tag(v___x_3216_))
{
case 0:
{
lean_object* v_key_3217_; uint8_t v___x_3218_; 
v_key_3217_ = lean_ctor_get(v___x_3216_, 0);
v___x_3218_ = lean_name_eq(v_x_3210_, v_key_3217_);
return v___x_3218_;
}
case 1:
{
lean_object* v_node_3219_; size_t v___x_3220_; size_t v___x_3221_; 
v_node_3219_ = lean_ctor_get(v___x_3216_, 0);
v___x_3220_ = ((size_t)5ULL);
v___x_3221_ = lean_usize_shift_right(v_x_3209_, v___x_3220_);
v_x_3208_ = v_node_3219_;
v_x_3209_ = v___x_3221_;
goto _start;
}
default: 
{
uint8_t v___x_3223_; 
v___x_3223_ = 0;
return v___x_3223_;
}
}
}
else
{
lean_object* v_ks_3224_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v_ks_3224_ = lean_ctor_get(v_x_3208_, 0);
v___x_3225_ = lean_unsigned_to_nat(0u);
v___x_3226_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_3224_, v___x_3225_, v_x_3210_);
return v___x_3226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_3227_, lean_object* v_x_3228_, lean_object* v_x_3229_){
_start:
{
size_t v_x_330__boxed_3230_; uint8_t v_res_3231_; lean_object* v_r_3232_; 
v_x_330__boxed_3230_ = lean_unbox_usize(v_x_3228_);
lean_dec(v_x_3228_);
v_res_3231_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3227_, v_x_330__boxed_3230_, v_x_3229_);
lean_dec(v_x_3229_);
lean_dec_ref(v_x_3227_);
v_r_3232_ = lean_box(v_res_3231_);
return v_r_3232_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_3233_, lean_object* v_x_3234_){
_start:
{
uint64_t v___y_3236_; 
if (lean_obj_tag(v_x_3234_) == 0)
{
uint64_t v___x_3239_; 
v___x_3239_ = 1723ULL;
v___y_3236_ = v___x_3239_;
goto v___jp_3235_;
}
else
{
uint64_t v_hash_3240_; 
v_hash_3240_ = lean_ctor_get_uint64(v_x_3234_, sizeof(void*)*2);
v___y_3236_ = v_hash_3240_;
goto v___jp_3235_;
}
v___jp_3235_:
{
size_t v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = lean_uint64_to_usize(v___y_3236_);
v___x_3238_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3233_, v___x_3237_, v_x_3234_);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_3241_, lean_object* v_x_3242_){
_start:
{
uint8_t v_res_3243_; lean_object* v_r_3244_; 
v_res_3243_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_3241_, v_x_3242_);
lean_dec(v_x_3242_);
lean_dec_ref(v_x_3241_);
v_r_3244_ = lean_box(v_res_3243_);
return v_r_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_3245_, lean_object* v_declName_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v_ext_3251_; lean_object* v_toEnvExtension_3252_; lean_object* v_env_3253_; lean_object* v_asyncMode_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; lean_object* v_extThms_3257_; uint8_t v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3249_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3250_ = lean_st_ref_get(v_a_3247_);
v_ext_3251_ = lean_ctor_get(v_ext_3245_, 1);
v_toEnvExtension_3252_ = lean_ctor_get(v_ext_3251_, 0);
v_env_3253_ = lean_ctor_get(v___x_3250_, 0);
lean_inc_ref(v_env_3253_);
lean_dec(v___x_3250_);
v_asyncMode_3254_ = lean_ctor_get(v_toEnvExtension_3252_, 2);
v___x_3255_ = 0;
v___x_3256_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3249_, v_ext_3245_, v_env_3253_, v_asyncMode_3254_, v___x_3255_);
v_extThms_3257_ = lean_ctor_get(v___x_3256_, 1);
lean_inc_ref(v_extThms_3257_);
lean_dec(v___x_3256_);
v___x_3258_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_3257_, v_declName_3246_);
lean_dec_ref(v_extThms_3257_);
v___x_3259_ = lean_box(v___x_3258_);
v___x_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_3261_, lean_object* v_declName_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3261_, v_declName_3262_, v_a_3263_);
lean_dec(v_a_3263_);
lean_dec(v_declName_3262_);
lean_dec_ref(v_ext_3261_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_3266_, lean_object* v_declName_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3266_, v_declName_3267_, v_a_3269_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_3272_, lean_object* v_declName_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_3272_, v_declName_3273_, v_a_3274_, v_a_3275_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_declName_3273_);
lean_dec_ref(v_ext_3272_);
return v_res_3277_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_){
_start:
{
uint8_t v___x_3281_; 
v___x_3281_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_3279_, v_x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_){
_start:
{
uint8_t v_res_3285_; lean_object* v_r_3286_; 
v_res_3285_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_3282_, v_x_3283_, v_x_3284_);
lean_dec(v_x_3284_);
lean_dec_ref(v_x_3283_);
v_r_3286_ = lean_box(v_res_3285_);
return v_r_3286_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_3287_, lean_object* v_x_3288_, size_t v_x_3289_, lean_object* v_x_3290_){
_start:
{
uint8_t v___x_3291_; 
v___x_3291_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3288_, v_x_3289_, v_x_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3292_, lean_object* v_x_3293_, lean_object* v_x_3294_, lean_object* v_x_3295_){
_start:
{
size_t v_x_417__boxed_3296_; uint8_t v_res_3297_; lean_object* v_r_3298_; 
v_x_417__boxed_3296_ = lean_unbox_usize(v_x_3294_);
lean_dec(v_x_3294_);
v_res_3297_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_3292_, v_x_3293_, v_x_417__boxed_3296_, v_x_3295_);
lean_dec(v_x_3295_);
lean_dec_ref(v_x_3293_);
v_r_3298_ = lean_box(v_res_3297_);
return v_r_3298_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3299_, lean_object* v_keys_3300_, lean_object* v_vals_3301_, lean_object* v_heq_3302_, lean_object* v_i_3303_, lean_object* v_k_3304_){
_start:
{
uint8_t v___x_3305_; 
v___x_3305_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_3300_, v_i_3303_, v_k_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3306_, lean_object* v_keys_3307_, lean_object* v_vals_3308_, lean_object* v_heq_3309_, lean_object* v_i_3310_, lean_object* v_k_3311_){
_start:
{
uint8_t v_res_3312_; lean_object* v_r_3313_; 
v_res_3312_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_3306_, v_keys_3307_, v_vals_3308_, v_heq_3309_, v_i_3310_, v_k_3311_);
lean_dec(v_k_3311_);
lean_dec_ref(v_vals_3308_);
lean_dec_ref(v_keys_3307_);
v_r_3313_ = lean_box(v_res_3312_);
return v_r_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_3314_, lean_object* v_declName_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v_ext_3320_; lean_object* v_toEnvExtension_3321_; lean_object* v_env_3322_; lean_object* v_asyncMode_3323_; uint8_t v___x_3324_; lean_object* v___x_3325_; lean_object* v_inj_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3318_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3319_ = lean_st_ref_get(v_a_3316_);
v_ext_3320_ = lean_ctor_get(v_ext_3314_, 1);
v_toEnvExtension_3321_ = lean_ctor_get(v_ext_3320_, 0);
v_env_3322_ = lean_ctor_get(v___x_3319_, 0);
lean_inc_ref(v_env_3322_);
lean_dec(v___x_3319_);
v_asyncMode_3323_ = lean_ctor_get(v_toEnvExtension_3321_, 2);
v___x_3324_ = 0;
v___x_3325_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3318_, v_ext_3314_, v_env_3322_, v_asyncMode_3323_, v___x_3324_);
v_inj_3326_ = lean_ctor_get(v___x_3325_, 4);
lean_inc_ref(v_inj_3326_);
lean_dec(v___x_3325_);
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v_declName_3315_);
v___x_3328_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_3326_, v___x_3327_);
lean_dec_ref_known(v___x_3327_, 1);
lean_dec_ref(v_inj_3326_);
v___x_3329_ = lean_box(v___x_3328_);
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_3331_, lean_object* v_declName_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3331_, v_declName_3332_, v_a_3333_);
lean_dec(v_a_3333_);
lean_dec_ref(v_ext_3331_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_3336_, lean_object* v_declName_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3336_, v_declName_3337_, v_a_3339_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_3342_, lean_object* v_declName_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_3342_, v_declName_3343_, v_a_3344_, v_a_3345_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec_ref(v_ext_3342_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_3348_, lean_object* v_declName_3349_, lean_object* v_a_3350_){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v_ext_3354_; lean_object* v_toEnvExtension_3355_; lean_object* v_env_3356_; lean_object* v_asyncMode_3357_; uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v_funCC_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3352_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3353_ = lean_st_ref_get(v_a_3350_);
v_ext_3354_ = lean_ctor_get(v_ext_3348_, 1);
v_toEnvExtension_3355_ = lean_ctor_get(v_ext_3354_, 0);
v_env_3356_ = lean_ctor_get(v___x_3353_, 0);
lean_inc_ref(v_env_3356_);
lean_dec(v___x_3353_);
v_asyncMode_3357_ = lean_ctor_get(v_toEnvExtension_3355_, 2);
v___x_3358_ = 0;
v___x_3359_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3352_, v_ext_3348_, v_env_3356_, v_asyncMode_3357_, v___x_3358_);
v_funCC_3360_ = lean_ctor_get(v___x_3359_, 2);
lean_inc(v_funCC_3360_);
lean_dec(v___x_3359_);
v___x_3361_ = l_Lean_NameSet_contains(v_funCC_3360_, v_declName_3349_);
lean_dec(v_funCC_3360_);
v___x_3362_ = lean_box(v___x_3361_);
v___x_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_3364_, lean_object* v_declName_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3364_, v_declName_3365_, v_a_3366_);
lean_dec(v_a_3366_);
lean_dec(v_declName_3365_);
lean_dec_ref(v_ext_3364_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_3369_, lean_object* v_declName_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3369_, v_declName_3370_, v_a_3372_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_3375_, lean_object* v_declName_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_3375_, v_declName_3376_, v_a_3377_, v_a_3378_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_declName_3376_);
lean_dec_ref(v_ext_3375_);
return v_res_3380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_3405_ = l_Lean_mkAtom(v___x_3404_);
return v___x_3405_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_3407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3408_ = lean_array_push(v___x_3407_, v___x_3406_);
return v___x_3408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_3418_ = l_Lean_mkAtom(v___x_3417_);
return v___x_3418_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3419_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_3420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3421_ = lean_array_push(v___x_3420_, v___x_3419_);
return v___x_3421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_3424_ = lean_box(2);
v___x_3425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v___x_3423_);
lean_ctor_set(v___x_3425_, 2, v___x_3422_);
return v___x_3425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3426_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_3427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_3428_ = lean_array_push(v___x_3427_, v___x_3426_);
return v___x_3428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3429_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_3430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_3431_ = lean_box(2);
v___x_3432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
lean_ctor_set(v___x_3432_, 1, v___x_3430_);
lean_ctor_set(v___x_3432_, 2, v___x_3429_);
return v___x_3432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_3434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3435_ = lean_array_push(v___x_3434_, v___x_3433_);
return v___x_3435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3436_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_3437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_3438_ = lean_box(2);
v___x_3439_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
lean_ctor_set(v___x_3439_, 1, v___x_3437_);
lean_ctor_set(v___x_3439_, 2, v___x_3436_);
return v___x_3439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_3441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3442_ = lean_array_push(v___x_3441_, v___x_3440_);
return v___x_3442_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_3444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_3445_ = lean_box(2);
v___x_3446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
lean_ctor_set(v___x_3446_, 1, v___x_3444_);
lean_ctor_set(v___x_3446_, 2, v___x_3443_);
return v___x_3446_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_3448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3449_ = lean_array_push(v___x_3448_, v___x_3447_);
return v___x_3449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_3451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_3452_ = lean_box(2);
v___x_3453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
lean_ctor_set(v___x_3453_, 1, v___x_3451_);
lean_ctor_set(v___x_3453_, 2, v___x_3450_);
return v___x_3453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_3455_, lean_object* v_ext_3456_, lean_object* v_____r_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
uint8_t v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = 0;
lean_inc(v_declName_3455_);
v___x_3464_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_3455_, v___x_3463_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; uint8_t v___x_3466_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref_known(v___x_3464_, 1);
v___x_3466_ = lean_unbox(v_a_3465_);
lean_dec(v_a_3465_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; lean_object* v_a_3468_; uint8_t v___x_3469_; 
v___x_3467_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3456_, v_declName_3455_, v___y_3461_);
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref(v___x_3467_);
v___x_3469_ = lean_unbox(v_a_3468_);
lean_dec(v_a_3468_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; lean_object* v_a_3471_; uint8_t v___x_3472_; 
lean_inc(v_declName_3455_);
v___x_3470_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3456_, v_declName_3455_, v___y_3461_);
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref(v___x_3470_);
v___x_3472_ = lean_unbox(v_a_3471_);
lean_dec(v_a_3471_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; lean_object* v_a_3474_; uint8_t v___x_3475_; 
v___x_3473_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3456_, v_declName_3455_, v___y_3461_);
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref(v___x_3473_);
v___x_3475_ = lean_unbox(v_a_3474_);
lean_dec(v_a_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
v___x_3476_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_3456_, v_declName_3455_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
return v___x_3476_;
}
else
{
lean_object* v___x_3477_; 
v___x_3477_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_3456_, v_declName_3455_, v___y_3460_, v___y_3461_);
return v___x_3477_;
}
}
else
{
lean_object* v___x_3478_; 
v___x_3478_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_3456_, v_declName_3455_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
return v___x_3478_;
}
}
else
{
lean_object* v___x_3479_; 
v___x_3479_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_3456_, v_declName_3455_, v___y_3460_, v___y_3461_);
return v___x_3479_;
}
}
else
{
lean_object* v___x_3480_; 
v___x_3480_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_3456_, v_declName_3455_, v___y_3460_, v___y_3461_);
return v___x_3480_;
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec_ref(v_ext_3456_);
lean_dec(v_declName_3455_);
v_a_3481_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3464_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3464_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_3489_, lean_object* v_ext_3490_, lean_object* v_____r_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_3489_, v_ext_3490_, v_____r_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_ref_3504_; lean_object* v___x_3505_; lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3514_; 
v_ref_3504_ = lean_ctor_get(v___y_3501_, 2);
v___x_3505_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msg_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3508_ = v___x_3505_;
v_isShared_3509_ = v_isSharedCheck_3514_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3514_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3512_; 
lean_inc(v_ref_3504_);
v___x_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3510_, 0, v_ref_3504_);
lean_ctor_set(v___x_3510_, 1, v_a_3506_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set_tag(v___x_3508_, 1);
lean_ctor_set(v___x_3508_, 0, v___x_3510_);
v___x_3512_ = v___x_3508_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
return v_res_3521_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3528_; uint64_t v___x_3529_; 
v___x_3528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_3529_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3528_);
return v___x_3529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_3531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_3532_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
lean_ctor_set_uint64(v___x_3532_, sizeof(void*)*1, v___x_3530_);
return v___x_3532_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
return v___x_3534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3535_ = lean_box(1);
v___x_3536_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_3537_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
lean_ctor_set(v___x_3538_, 1, v___x_3536_);
lean_ctor_set(v___x_3538_, 2, v___x_3535_);
return v___x_3538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3542_ = lean_unsigned_to_nat(0u);
v___x_3543_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
lean_ctor_set(v___x_3543_, 2, v___x_3542_);
lean_ctor_set(v___x_3543_, 3, v___x_3542_);
lean_ctor_set(v___x_3543_, 4, v___x_3541_);
lean_ctor_set(v___x_3543_, 5, v___x_3541_);
lean_ctor_set(v___x_3543_, 6, v___x_3541_);
lean_ctor_set(v___x_3543_, 7, v___x_3541_);
lean_ctor_set(v___x_3543_, 8, v___x_3541_);
lean_ctor_set(v___x_3543_, 9, v___x_3541_);
lean_ctor_set(v___x_3543_, 10, v___x_3541_);
return v___x_3543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
return v___x_3545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = lean_unsigned_to_nat(0u);
v___x_3547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
lean_ctor_set(v___x_3548_, 2, v___x_3546_);
return v___x_3548_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3552_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
v___x_3553_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3552_);
lean_ctor_set(v___x_3553_, 1, v___x_3551_);
lean_ctor_set(v___x_3553_, 2, v___x_3550_);
lean_ctor_set(v___x_3553_, 3, v___x_3551_);
lean_ctor_set(v___x_3553_, 4, v___x_3551_);
lean_ctor_set(v___x_3553_, 5, v___x_3551_);
lean_ctor_set(v___x_3553_, 6, v___x_3551_);
lean_ctor_set(v___x_3553_, 7, v___x_3549_);
return v___x_3553_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
lean_ctor_set(v___x_3555_, 2, v___x_3554_);
lean_ctor_set(v___x_3555_, 3, v___x_3554_);
lean_ctor_set(v___x_3555_, 4, v___x_3554_);
return v___x_3555_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11));
v___x_3558_ = l_Lean_stringToMessageData(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13));
v___x_3561_ = l_Lean_stringToMessageData(v___x_3560_);
return v___x_3561_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v_ext_3565_, lean_object* v___x_3566_, uint8_t v_showInfo_3567_, lean_object* v_attrName_3568_, lean_object* v_declName_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
uint8_t v___x_3573_; uint8_t v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___y_3588_; 
v___x_3573_ = 1;
v___x_3574_ = 0;
v___x_3575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3576_ = lean_unsigned_to_nat(0u);
v___x_3577_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_3578_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_3579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_3580_ = lean_box(0);
lean_inc(v___x_3566_);
v___x_3581_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3581_, 0, v___x_3575_);
lean_ctor_set(v___x_3581_, 1, v___x_3566_);
lean_ctor_set(v___x_3581_, 2, v___x_3578_);
lean_ctor_set(v___x_3581_, 3, v___x_3579_);
lean_ctor_set(v___x_3581_, 4, v___x_3580_);
lean_ctor_set(v___x_3581_, 5, v___x_3576_);
lean_ctor_set(v___x_3581_, 6, v___x_3580_);
lean_ctor_set_uint8(v___x_3581_, sizeof(void*)*7, v___x_3574_);
lean_ctor_set_uint8(v___x_3581_, sizeof(void*)*7 + 1, v___x_3574_);
lean_ctor_set_uint8(v___x_3581_, sizeof(void*)*7 + 2, v___x_3574_);
lean_ctor_set_uint8(v___x_3581_, sizeof(void*)*7 + 3, v___x_3573_);
v___x_3582_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_3583_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_3584_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_3585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3582_);
lean_ctor_set(v___x_3585_, 1, v___x_3583_);
lean_ctor_set(v___x_3585_, 2, v___x_3566_);
lean_ctor_set(v___x_3585_, 3, v___x_3577_);
lean_ctor_set(v___x_3585_, 4, v___x_3584_);
v___x_3586_ = lean_st_mk_ref(v___x_3585_);
if (v_showInfo_3567_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_dec(v_attrName_3568_);
v___x_3598_ = lean_box(0);
v___x_3599_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_3569_, v_ext_3565_, v___x_3598_, v___x_3581_, v___x_3586_, v___y_3570_, v___y_3571_);
lean_dec_ref_known(v___x_3581_, 7);
v___y_3588_ = v___x_3599_;
goto v___jp_3587_;
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_dec(v_declName_3569_);
lean_dec_ref(v_ext_3565_);
v___x_3600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12);
v___x_3601_ = l_Lean_MessageData_ofName(v_attrName_3568_);
lean_inc_ref(v___x_3601_);
v___x_3602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14);
v___x_3604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3602_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
lean_ctor_set(v___x_3605_, 1, v___x_3601_);
v___x_3606_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__16);
v___x_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3607_, v___x_3581_, v___x_3586_, v___y_3570_, v___y_3571_);
lean_dec(v___x_3586_);
lean_dec_ref_known(v___x_3581_, 7);
return v___x_3608_;
}
v___jp_3587_:
{
if (lean_obj_tag(v___y_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3597_; 
v_a_3589_ = lean_ctor_get(v___y_3588_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___y_3588_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3591_ = v___y_3588_;
v_isShared_3592_ = v_isSharedCheck_3597_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___y_3588_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3597_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3593_ = lean_st_ref_get(v___x_3586_);
lean_dec(v___x_3586_);
lean_dec(v___x_3593_);
if (v_isShared_3592_ == 0)
{
v___x_3595_ = v___x_3591_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3589_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
else
{
lean_dec(v___x_3586_);
return v___y_3588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v_ext_3609_, lean_object* v___x_3610_, lean_object* v_showInfo_3611_, lean_object* v_attrName_3612_, lean_object* v_declName_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
uint8_t v_showInfo_boxed_3617_; lean_object* v_res_3618_; 
v_showInfo_boxed_3617_ = lean_unbox(v_showInfo_3611_);
v_res_3618_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v_ext_3609_, v___x_3610_, v_showInfo_boxed_3617_, v_attrName_3612_, v_declName_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_3621_, uint8_t v_attrKind_3622_, uint8_t v_showInfo_3623_, uint8_t v_minIndexable_3624_, lean_object* v_as_x27_3625_, lean_object* v_b_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
if (lean_obj_tag(v_as_x27_3625_) == 0)
{
lean_object* v___x_3632_; 
lean_dec_ref(v_ext_3621_);
v___x_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3632_, 0, v_b_3626_);
return v___x_3632_;
}
else
{
lean_object* v_head_3633_; lean_object* v_tail_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v_head_3633_ = lean_ctor_get(v_as_x27_3625_, 0);
v_tail_3634_ = lean_ctor_get(v_as_x27_3625_, 1);
v___x_3635_ = lean_box(0);
v___x_3636_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3630_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v___x_3638_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_3633_);
lean_inc_ref(v_ext_3621_);
v___x_3639_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_3621_, v_head_3633_, v_attrKind_3622_, v___x_3638_, v_a_3637_, v_showInfo_3623_, v_minIndexable_3624_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_dec_ref_known(v___x_3639_, 1);
v_as_x27_3625_ = v_tail_3634_;
v_b_3626_ = v___x_3635_;
goto _start;
}
else
{
lean_dec_ref(v_ext_3621_);
return v___x_3639_;
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_dec_ref(v_ext_3621_);
v_a_3641_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3636_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3636_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_3649_, lean_object* v_attrKind_3650_, lean_object* v_showInfo_3651_, lean_object* v_minIndexable_3652_, lean_object* v_as_x27_3653_, lean_object* v_b_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
uint8_t v_attrKind_boxed_3660_; uint8_t v_showInfo_boxed_3661_; uint8_t v_minIndexable_boxed_3662_; lean_object* v_res_3663_; 
v_attrKind_boxed_3660_ = lean_unbox(v_attrKind_3650_);
v_showInfo_boxed_3661_ = lean_unbox(v_showInfo_3651_);
v_minIndexable_boxed_3662_ = lean_unbox(v_minIndexable_3652_);
v_res_3663_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3649_, v_attrKind_boxed_3660_, v_showInfo_boxed_3661_, v_minIndexable_boxed_3662_, v_as_x27_3653_, v_b_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v_as_x27_3653_);
return v_res_3663_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_3666_ = l_Lean_stringToMessageData(v___x_3665_);
return v___x_3666_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_3669_ = l_Lean_stringToMessageData(v___x_3668_);
return v___x_3669_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_3672_ = l_Lean_stringToMessageData(v___x_3671_);
return v___x_3672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_3675_ = l_Lean_stringToMessageData(v___x_3674_);
return v___x_3675_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_3680_ = l_Lean_stringToMessageData(v___x_3679_);
return v___x_3680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_3683_ = l_Lean_stringToMessageData(v___x_3682_);
return v___x_3683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14(void){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13));
v___x_3686_ = l_Lean_stringToMessageData(v___x_3685_);
return v___x_3686_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16(void){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15));
v___x_3689_ = l_Lean_stringToMessageData(v___x_3688_);
return v___x_3689_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18(void){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17));
v___x_3692_ = l_Lean_stringToMessageData(v___x_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_declName_3693_, uint8_t v_attrKind_3694_, lean_object* v_stx_3695_, lean_object* v_ext_3696_, uint8_t v_showInfo_3697_, uint8_t v_minIndexable_3698_, uint8_t v___x_3699_, lean_object* v_attrName_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_3695_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_a_3729_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3729_);
lean_dec_ref_known(v___x_3728_, 1);
switch(lean_obj_tag(v_a_3729_))
{
case 0:
{
lean_object* v_k_3730_; 
lean_dec(v_attrName_3700_);
lean_dec(v_stx_3695_);
v_k_3730_ = lean_ctor_get(v_a_3729_, 0);
lean_inc(v_k_3730_);
lean_dec_ref_known(v_a_3729_, 1);
if (lean_obj_tag(v_k_3730_) == 9)
{
lean_object* v___x_3731_; 
lean_dec_ref(v_ext_3696_);
lean_dec(v_declName_3693_);
v___x_3731_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_3703_, v___y_3704_);
return v___x_3731_;
}
else
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3704_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3734_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___x_3732_, 1);
v___x_3734_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_3696_, v_declName_3693_, v_attrKind_3694_, v_k_3730_, v_a_3733_, v_showInfo_3697_, v_minIndexable_3698_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3734_;
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec(v_k_3730_);
lean_dec_ref(v_ext_3696_);
lean_dec(v_declName_3693_);
v_a_3735_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3732_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3732_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_3743_; lean_object* v___x_3744_; 
lean_dec(v_attrName_3700_);
lean_dec(v_stx_3695_);
v_eager_3743_ = lean_ctor_get_uint8(v_a_3729_, 0);
lean_dec_ref_known(v_a_3729_, 0);
v___x_3744_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_3696_, v_declName_3693_, v_eager_3743_, v_attrKind_3694_, v___y_3703_, v___y_3704_);
return v___x_3744_;
}
case 2:
{
lean_object* v___x_3745_; 
lean_dec(v_stx_3695_);
lean_inc(v_declName_3693_);
v___x_3745_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_3693_, v___x_3699_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
if (lean_obj_tag(v_a_3746_) == 1)
{
lean_object* v_val_3747_; lean_object* v_ctors_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_dec(v_attrName_3700_);
lean_dec(v_declName_3693_);
v_val_3747_ = lean_ctor_get(v_a_3746_, 0);
lean_inc(v_val_3747_);
lean_dec_ref_known(v_a_3746_, 1);
v_ctors_3748_ = lean_ctor_get(v_val_3747_, 4);
lean_inc(v_ctors_3748_);
lean_dec(v_val_3747_);
v___x_3749_ = lean_box(0);
v___x_3750_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3696_, v_attrKind_3694_, v_showInfo_3697_, v_minIndexable_3698_, v_ctors_3748_, v___x_3749_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec(v_ctors_3748_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; 
v_unused_3758_ = lean_ctor_get(v___x_3750_, 0);
lean_dec(v_unused_3758_);
v___x_3752_ = v___x_3750_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_dec(v___x_3750_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3749_);
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3749_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
else
{
return v___x_3750_;
}
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
lean_dec(v_a_3746_);
lean_dec_ref(v_ext_3696_);
v___x_3759_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_3760_ = l_Lean_MessageData_ofName(v_attrName_3700_);
v___x_3761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_3763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = l_Lean_MessageData_ofConstName(v_declName_3693_, v___x_3699_);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3765_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3767_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3768_;
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec(v_attrName_3700_);
lean_dec_ref(v_ext_3696_);
lean_dec(v_declName_3693_);
v_a_3769_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3745_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3745_);
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
case 3:
{
lean_object* v___x_3777_; 
lean_dec(v_attrName_3700_);
lean_inc(v_declName_3693_);
v___x_3777_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_3693_, v___x_3699_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___x_3777_, 1);
if (lean_obj_tag(v_a_3778_) == 1)
{
lean_object* v_val_3779_; lean_object* v___x_3780_; 
lean_dec(v_stx_3695_);
lean_dec(v_declName_3693_);
v_val_3779_ = lean_ctor_get(v_a_3778_, 0);
lean_inc_n(v_val_3779_, 2);
lean_dec_ref_known(v_a_3778_, 1);
lean_inc_ref(v_ext_3696_);
v___x_3780_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_3696_, v_val_3779_, v___x_3699_, v_attrKind_3694_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v___x_3781_; 
lean_dec_ref_known(v___x_3780_, 1);
v___x_3781_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3779_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3802_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3784_ = v___x_3781_;
v_isShared_3785_ = v_isSharedCheck_3802_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3781_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3802_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
if (lean_obj_tag(v_a_3782_) == 1)
{
lean_object* v_val_3786_; lean_object* v_ctors_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
lean_del_object(v___x_3784_);
v_val_3786_ = lean_ctor_get(v_a_3782_, 0);
lean_inc(v_val_3786_);
lean_dec_ref_known(v_a_3782_, 1);
v_ctors_3787_ = lean_ctor_get(v_val_3786_, 4);
lean_inc(v_ctors_3787_);
lean_dec(v_val_3786_);
v___x_3788_ = lean_box(0);
v___x_3789_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3696_, v_attrKind_3694_, v_showInfo_3697_, v_minIndexable_3698_, v_ctors_3787_, v___x_3788_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec(v_ctors_3787_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; 
v_unused_3797_ = lean_ctor_get(v___x_3789_, 0);
lean_dec(v_unused_3797_);
v___x_3791_ = v___x_3789_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_dec(v___x_3789_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3788_);
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3788_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
else
{
return v___x_3789_;
}
}
else
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
lean_dec(v_a_3782_);
lean_dec_ref(v_ext_3696_);
v___x_3798_ = lean_box(0);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3798_);
v___x_3800_ = v___x_3784_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec_ref(v_ext_3696_);
v_a_3803_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3781_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3781_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_dec(v_val_3779_);
lean_dec_ref(v_ext_3696_);
return v___x_3780_;
}
}
else
{
lean_object* v___x_3811_; 
lean_dec(v_a_3778_);
v___x_3811_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3704_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3813_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3812_);
lean_dec_ref_known(v___x_3811_, 1);
v___x_3813_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_3696_, v_stx_3695_, v_declName_3693_, v_attrKind_3694_, v_a_3812_, v_minIndexable_3698_, v_showInfo_3697_, v___x_3699_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3813_;
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref(v_ext_3696_);
lean_dec(v_stx_3695_);
lean_dec(v_declName_3693_);
v_a_3814_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3811_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3811_);
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
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref(v_ext_3696_);
lean_dec(v_stx_3695_);
lean_dec(v_declName_3693_);
v_a_3822_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3777_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3777_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
case 4:
{
lean_object* v___x_3830_; 
lean_dec(v_attrName_3700_);
lean_dec(v_stx_3695_);
v___x_3830_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_3696_, v_declName_3693_, v_attrKind_3694_, v___y_3703_, v___y_3704_);
return v___x_3830_;
}
case 5:
{
lean_object* v_prio_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
lean_dec_ref(v_ext_3696_);
lean_dec(v_stx_3695_);
v_prio_3831_ = lean_ctor_get(v_a_3729_, 0);
lean_inc(v_prio_3831_);
lean_dec_ref_known(v_a_3729_, 1);
v___x_3832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3833_ = lean_name_eq(v_attrName_3700_, v___x_3832_);
lean_dec(v_attrName_3700_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
lean_dec(v_prio_3831_);
lean_dec(v_declName_3693_);
v___x_3834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10);
v___x_3835_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3834_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3835_;
}
else
{
lean_object* v___x_3836_; 
v___x_3836_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_3693_, v_attrKind_3694_, v_prio_3831_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3836_;
}
}
case 6:
{
lean_object* v___x_3837_; 
lean_dec(v_attrName_3700_);
lean_dec(v_stx_3695_);
v___x_3837_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_3696_, v_declName_3693_, v_attrKind_3694_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3837_;
}
case 7:
{
lean_object* v___x_3838_; 
lean_dec(v_attrName_3700_);
lean_dec(v_stx_3695_);
v___x_3838_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_3696_, v_declName_3693_, v_attrKind_3694_, v___y_3703_, v___y_3704_);
return v___x_3838_;
}
case 8:
{
uint8_t v_post_3839_; uint8_t v_inv_3840_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___x_3848_; uint8_t v___x_3849_; 
lean_dec_ref(v_ext_3696_);
lean_dec(v_stx_3695_);
v_post_3839_ = lean_ctor_get_uint8(v_a_3729_, 0);
v_inv_3840_ = lean_ctor_get_uint8(v_a_3729_, 1);
lean_dec_ref_known(v_a_3729_, 0);
v___x_3848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3849_ = lean_name_eq(v_attrName_3700_, v___x_3848_);
lean_dec(v_attrName_3700_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_dec(v_declName_3693_);
v___x_3850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12);
v___x_3851_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3850_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3851_;
}
else
{
v___y_3842_ = v___y_3701_;
v___y_3843_ = v___y_3702_;
v___y_3844_ = v___y_3703_;
v___y_3845_ = v___y_3704_;
goto v___jp_3841_;
}
v___jp_3841_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = lean_unsigned_to_nat(1000u);
v___x_3847_ = l_Lean_Meta_Grind_addNormTheorem(v_declName_3693_, v_post_3839_, v_inv_3840_, v_attrKind_3694_, v___x_3846_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
return v___x_3847_;
}
}
case 9:
{
lean_object* v___x_3852_; uint8_t v___x_3853_; 
lean_dec_ref(v_ext_3696_);
lean_dec(v_stx_3695_);
v___x_3852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3853_ = lean_name_eq(v_attrName_3700_, v___x_3852_);
lean_dec(v_attrName_3700_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_dec(v_declName_3693_);
v___x_3854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14);
v___x_3855_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3854_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3855_;
}
else
{
goto v___jp_3706_;
}
}
case 10:
{
uint8_t v_fallback_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
lean_dec_ref(v_ext_3696_);
lean_dec(v_stx_3695_);
v_fallback_3856_ = lean_ctor_get_uint8(v_a_3729_, 0);
lean_dec_ref_known(v_a_3729_, 0);
v___x_3857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3858_ = lean_name_eq(v_attrName_3700_, v___x_3857_);
lean_dec(v_attrName_3700_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
lean_dec(v_declName_3693_);
v___x_3859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16);
v___x_3860_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3859_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3860_;
}
else
{
lean_object* v___x_3861_; 
v___x_3861_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_3693_, v_attrKind_3694_, v_fallback_3856_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3861_;
}
}
default: 
{
lean_object* v___x_3862_; uint8_t v___x_3863_; 
lean_dec_ref(v_ext_3696_);
lean_dec(v_stx_3695_);
v___x_3862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3863_ = lean_name_eq(v_attrName_3700_, v___x_3862_);
lean_dec(v_attrName_3700_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
lean_dec(v_declName_3693_);
v___x_3864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18);
v___x_3865_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3864_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3865_;
}
else
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_3693_, v_attrKind_3694_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3866_;
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_dec(v_attrName_3700_);
lean_dec_ref(v_ext_3696_);
lean_dec(v_stx_3695_);
lean_dec(v_declName_3693_);
v_a_3867_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3728_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3728_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
v___jp_3706_:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_Meta_Grind_addNormDeclToUnfold(v_declName_3693_, v_attrKind_3694_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3719_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3710_ = v___x_3707_;
v_isShared_3711_ = v_isSharedCheck_3719_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3719_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
uint8_t v___x_3712_; 
v___x_3712_ = lean_unbox(v_a_3708_);
lean_dec(v_a_3708_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_del_object(v___x_3710_);
v___x_3713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_3714_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3713_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3714_;
}
else
{
lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3715_ = lean_box(0);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3715_);
v___x_3717_ = v___x_3710_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
v_a_3720_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3707_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3707_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_declName_3875_, lean_object* v_attrKind_3876_, lean_object* v_stx_3877_, lean_object* v_ext_3878_, lean_object* v_showInfo_3879_, lean_object* v_minIndexable_3880_, lean_object* v___x_3881_, lean_object* v_attrName_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
uint8_t v_attrKind_boxed_3888_; uint8_t v_showInfo_boxed_3889_; uint8_t v_minIndexable_boxed_3890_; uint8_t v___x_12273__boxed_3891_; lean_object* v_res_3892_; 
v_attrKind_boxed_3888_ = lean_unbox(v_attrKind_3876_);
v_showInfo_boxed_3889_ = lean_unbox(v_showInfo_3879_);
v_minIndexable_boxed_3890_ = lean_unbox(v_minIndexable_3880_);
v___x_12273__boxed_3891_ = lean_unbox(v___x_3881_);
v_res_3892_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_declName_3875_, v_attrKind_boxed_3888_, v_stx_3877_, v_ext_3878_, v_showInfo_boxed_3889_, v_minIndexable_boxed_3890_, v___x_12273__boxed_3891_, v_attrName_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0(lean_object* v___x_3893_, lean_object* v_entry_3894_, lean_object* v_s_3895_){
_start:
{
lean_object* v_addEntryFn_3896_; lean_object* v_importedEntries_3897_; lean_object* v_state_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3906_; 
v_addEntryFn_3896_ = lean_ctor_get(v___x_3893_, 3);
lean_inc(v_addEntryFn_3896_);
lean_dec_ref(v___x_3893_);
v_importedEntries_3897_ = lean_ctor_get(v_s_3895_, 0);
v_state_3898_ = lean_ctor_get(v_s_3895_, 1);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_s_3895_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3900_ = v_s_3895_;
v_isShared_3901_ = v_isSharedCheck_3906_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_state_3898_);
lean_inc(v_importedEntries_3897_);
lean_dec(v_s_3895_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3906_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_state_3902_; lean_object* v___x_3904_; 
v_state_3902_ = lean_apply_2(v_addEntryFn_3896_, v_state_3898_, v_entry_3894_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 1, v_state_3902_);
v___x_3904_ = v___x_3900_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_importedEntries_3897_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_state_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_keys_3907_, lean_object* v_i_3908_, lean_object* v_k_3909_){
_start:
{
lean_object* v___x_3910_; uint8_t v___x_3911_; 
v___x_3910_ = lean_array_get_size(v_keys_3907_);
v___x_3911_ = lean_nat_dec_lt(v_i_3908_, v___x_3910_);
if (v___x_3911_ == 0)
{
lean_dec(v_i_3908_);
return v___x_3911_;
}
else
{
lean_object* v_k_x27_3912_; uint8_t v___x_3913_; 
v_k_x27_3912_ = lean_array_fget_borrowed(v_keys_3907_, v_i_3908_);
v___x_3913_ = l_Lean_instBEqExtraModUse_beq(v_k_3909_, v_k_x27_3912_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = lean_unsigned_to_nat(1u);
v___x_3915_ = lean_nat_add(v_i_3908_, v___x_3914_);
lean_dec(v_i_3908_);
v_i_3908_ = v___x_3915_;
goto _start;
}
else
{
lean_dec(v_i_3908_);
return v___x_3911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_keys_3917_, lean_object* v_i_3918_, lean_object* v_k_3919_){
_start:
{
uint8_t v_res_3920_; lean_object* v_r_3921_; 
v_res_3920_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_keys_3917_, v_i_3918_, v_k_3919_);
lean_dec_ref(v_k_3919_);
lean_dec_ref(v_keys_3917_);
v_r_3921_ = lean_box(v_res_3920_);
return v_r_3921_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3922_, size_t v_x_3923_, lean_object* v_x_3924_){
_start:
{
if (lean_obj_tag(v_x_3922_) == 0)
{
lean_object* v_es_3925_; lean_object* v___x_3926_; size_t v___x_3927_; size_t v___x_3928_; lean_object* v_j_3929_; lean_object* v___x_3930_; 
v_es_3925_ = lean_ctor_get(v_x_3922_, 0);
v___x_3926_ = lean_box(2);
v___x_3927_ = ((size_t)31ULL);
v___x_3928_ = lean_usize_land(v_x_3923_, v___x_3927_);
v_j_3929_ = lean_usize_to_nat(v___x_3928_);
v___x_3930_ = lean_array_get_borrowed(v___x_3926_, v_es_3925_, v_j_3929_);
lean_dec(v_j_3929_);
switch(lean_obj_tag(v___x_3930_))
{
case 0:
{
lean_object* v_key_3931_; uint8_t v___x_3932_; 
v_key_3931_ = lean_ctor_get(v___x_3930_, 0);
v___x_3932_ = l_Lean_instBEqExtraModUse_beq(v_x_3924_, v_key_3931_);
return v___x_3932_;
}
case 1:
{
lean_object* v_node_3933_; size_t v___x_3934_; size_t v___x_3935_; 
v_node_3933_ = lean_ctor_get(v___x_3930_, 0);
v___x_3934_ = ((size_t)5ULL);
v___x_3935_ = lean_usize_shift_right(v_x_3923_, v___x_3934_);
v_x_3922_ = v_node_3933_;
v_x_3923_ = v___x_3935_;
goto _start;
}
default: 
{
uint8_t v___x_3937_; 
v___x_3937_ = 0;
return v___x_3937_;
}
}
}
else
{
lean_object* v_ks_3938_; lean_object* v___x_3939_; uint8_t v___x_3940_; 
v_ks_3938_ = lean_ctor_get(v_x_3922_, 0);
v___x_3939_ = lean_unsigned_to_nat(0u);
v___x_3940_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_ks_3938_, v___x_3939_, v_x_3924_);
return v___x_3940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_x_3941_, lean_object* v_x_3942_, lean_object* v_x_3943_){
_start:
{
size_t v_x_12699__boxed_3944_; uint8_t v_res_3945_; lean_object* v_r_3946_; 
v_x_12699__boxed_3944_ = lean_unbox_usize(v_x_3942_);
lean_dec(v_x_3942_);
v_res_3945_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_3941_, v_x_12699__boxed_3944_, v_x_3943_);
lean_dec_ref(v_x_3943_);
lean_dec_ref(v_x_3941_);
v_r_3946_ = lean_box(v_res_3945_);
return v_r_3946_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3947_, lean_object* v_x_3948_){
_start:
{
uint64_t v___x_3949_; size_t v___x_3950_; uint8_t v___x_3951_; 
v___x_3949_ = l_Lean_instHashableExtraModUse_hash(v_x_3948_);
v___x_3950_ = lean_uint64_to_usize(v___x_3949_);
v___x_3951_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_3947_, v___x_3950_, v_x_3948_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3952_, lean_object* v_x_3953_){
_start:
{
uint8_t v_res_3954_; lean_object* v_r_3955_; 
v_res_3954_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v_x_3952_, v_x_3953_);
lean_dec_ref(v_x_3953_);
lean_dec_ref(v_x_3952_);
v_r_3955_ = lean_box(v_res_3954_);
return v_r_3955_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_3956_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3));
v___x_3962_ = l_Lean_stringToMessageData(v___x_3961_);
return v___x_3962_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5));
v___x_3965_ = l_Lean_stringToMessageData(v___x_3964_);
return v___x_3965_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_3967_ = l_Lean_stringToMessageData(v___x_3966_);
return v___x_3967_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v_cls_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_cls_3968_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_3969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1));
v___x_3970_ = l_Lean_Name_append(v___x_3969_, v_cls_3968_);
return v___x_3970_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9));
v___x_3973_ = l_Lean_stringToMessageData(v___x_3972_);
return v___x_3973_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12(void){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11));
v___x_3976_ = l_Lean_stringToMessageData(v___x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(lean_object* v_mod_3981_, uint8_t v_isMeta_3982_, lean_object* v_hint_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v_env_4023_; uint8_t v_isExporting_4024_; lean_object* v_entry_4025_; lean_object* v___x_4026_; lean_object* v_env_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; uint8_t v___x_4032_; 
v___x_4021_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0);
v___x_4022_ = lean_st_ref_get(v___y_3987_);
v_env_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc_ref(v_env_4023_);
lean_dec(v___x_4022_);
v_isExporting_4024_ = lean_ctor_get_uint8(v_env_4023_, sizeof(void*)*13);
lean_dec_ref(v_env_4023_);
lean_inc(v_mod_3981_);
v_entry_4025_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_4025_, 0, v_mod_3981_);
lean_ctor_set_uint8(v_entry_4025_, sizeof(void*)*1, v_isExporting_4024_);
lean_ctor_set_uint8(v_entry_4025_, sizeof(void*)*1 + 1, v_isMeta_3982_);
v___x_4026_ = lean_st_ref_get(v___y_3987_);
v_env_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc_ref(v_env_4027_);
lean_dec(v___x_4026_);
v___x_4028_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_4029_ = lean_box(1);
v___x_4030_ = lean_box(0);
v___x_4031_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4021_, v___x_4028_, v_env_4027_, v___x_4029_, v___x_4030_);
v___x_4032_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v___x_4031_, v_entry_4025_);
lean_dec(v___x_4031_);
if (v___x_4032_ == 0)
{
lean_object* v_toCold_4033_; lean_object* v_options_4034_; lean_object* v_inheritedTraceOptions_4035_; uint8_t v_hasTrace_4036_; lean_object* v___f_4037_; uint8_t v___x_4038_; lean_object* v___y_4040_; lean_object* v___y_4041_; 
v_toCold_4033_ = lean_ctor_get(v___y_3986_, 0);
v_options_4034_ = lean_ctor_get(v_toCold_4033_, 2);
v_inheritedTraceOptions_4035_ = lean_ctor_get(v_toCold_4033_, 11);
v_hasTrace_4036_ = lean_ctor_get_uint8(v_options_4034_, sizeof(void*)*1);
v___f_4037_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_4037_, 0, v___x_4028_);
lean_closure_set(v___f_4037_, 1, v_entry_4025_);
v___x_4038_ = 1;
if (v_hasTrace_4036_ == 0)
{
lean_dec(v_hint_3983_);
lean_dec(v_mod_3981_);
v___y_4040_ = v___y_3985_;
v___y_4041_ = v___y_3987_;
goto v___jp_4039_;
}
else
{
lean_object* v_cls_4068_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___x_4088_; uint8_t v___x_4089_; 
v_cls_4068_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_4088_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8);
v___x_4089_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4035_, v_options_4034_, v___x_4088_);
if (v___x_4089_ == 0)
{
lean_dec(v_hint_3983_);
lean_dec(v_mod_3981_);
v___y_4040_ = v___y_3985_;
v___y_4041_ = v___y_3987_;
goto v___jp_4039_;
}
else
{
lean_object* v___x_4090_; lean_object* v___y_4092_; 
v___x_4090_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10);
if (v_isExporting_4024_ == 0)
{
lean_object* v___x_4099_; 
v___x_4099_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15));
v___y_4092_ = v___x_4099_;
goto v___jp_4091_;
}
else
{
lean_object* v___x_4100_; 
v___x_4100_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16));
v___y_4092_ = v___x_4100_;
goto v___jp_4091_;
}
v___jp_4091_:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
lean_inc_ref(v___y_4092_);
v___x_4093_ = l_Lean_stringToMessageData(v___y_4092_);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4090_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12);
v___x_4096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4094_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
if (v_isMeta_3982_ == 0)
{
lean_object* v___x_4097_; 
v___x_4097_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13));
v___y_4075_ = v___x_4096_;
v___y_4076_ = v___x_4097_;
goto v___jp_4074_;
}
else
{
lean_object* v___x_4098_; 
v___x_4098_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14));
v___y_4075_ = v___x_4096_;
v___y_4076_ = v___x_4098_;
goto v___jp_4074_;
}
}
}
v___jp_4069_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___y_4070_);
lean_ctor_set(v___x_4072_, 1, v___y_4071_);
v___x_4073_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_4068_, v___x_4072_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_dec_ref_known(v___x_4073_, 1);
v___y_4040_ = v___y_3985_;
v___y_4041_ = v___y_3987_;
goto v___jp_4039_;
}
else
{
lean_dec_ref(v___f_4037_);
return v___x_4073_;
}
}
v___jp_4074_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; 
lean_inc_ref(v___y_4076_);
v___x_4077_ = l_Lean_stringToMessageData(v___y_4076_);
v___x_4078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___y_4075_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
v___x_4079_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4);
v___x_4080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4078_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = l_Lean_MessageData_ofName(v_mod_3981_);
v___x_4082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4080_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = l_Lean_Name_isAnonymous(v_hint_3983_);
if (v___x_4083_ == 0)
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6);
v___x_4085_ = l_Lean_MessageData_ofName(v_hint_3983_);
v___x_4086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4084_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
v___y_4070_ = v___x_4082_;
v___y_4071_ = v___x_4086_;
goto v___jp_4069_;
}
else
{
lean_object* v___x_4087_; 
lean_dec(v_hint_3983_);
v___x_4087_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7);
v___y_4070_ = v___x_4082_;
v___y_4071_ = v___x_4087_;
goto v___jp_4069_;
}
}
}
v___jp_4039_:
{
lean_object* v___x_4042_; lean_object* v_toEnvExtension_4043_; uint8_t v_logWrites_4044_; 
v___x_4042_ = lean_st_ref_take(v___y_4041_);
v_toEnvExtension_4043_ = lean_ctor_get(v___x_4028_, 0);
v_logWrites_4044_ = lean_ctor_get_uint8(v_toEnvExtension_4043_, sizeof(void*)*6);
if (v_logWrites_4044_ == 0)
{
lean_object* v_env_4045_; lean_object* v_nextMacroScope_4046_; lean_object* v_ngen_4047_; lean_object* v_auxDeclNGen_4048_; lean_object* v_traceState_4049_; lean_object* v_recordedDeps_4050_; lean_object* v_messages_4051_; lean_object* v_infoState_4052_; lean_object* v_snapshotTasks_4053_; lean_object* v_asyncMode_4054_; lean_object* v___x_4055_; 
v_env_4045_ = lean_ctor_get(v___x_4042_, 0);
lean_inc_ref(v_env_4045_);
v_nextMacroScope_4046_ = lean_ctor_get(v___x_4042_, 1);
lean_inc(v_nextMacroScope_4046_);
v_ngen_4047_ = lean_ctor_get(v___x_4042_, 2);
lean_inc_ref(v_ngen_4047_);
v_auxDeclNGen_4048_ = lean_ctor_get(v___x_4042_, 3);
lean_inc_ref(v_auxDeclNGen_4048_);
v_traceState_4049_ = lean_ctor_get(v___x_4042_, 4);
lean_inc_ref(v_traceState_4049_);
v_recordedDeps_4050_ = lean_ctor_get(v___x_4042_, 6);
lean_inc_ref(v_recordedDeps_4050_);
v_messages_4051_ = lean_ctor_get(v___x_4042_, 7);
lean_inc_ref(v_messages_4051_);
v_infoState_4052_ = lean_ctor_get(v___x_4042_, 8);
lean_inc_ref(v_infoState_4052_);
v_snapshotTasks_4053_ = lean_ctor_get(v___x_4042_, 9);
lean_inc_ref(v_snapshotTasks_4053_);
lean_dec(v___x_4042_);
v_asyncMode_4054_ = lean_ctor_get(v_toEnvExtension_4043_, 2);
lean_inc_ref(v_toEnvExtension_4043_);
v___x_4055_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4043_, v_env_4045_, v___f_4037_, v_asyncMode_4054_, v___x_4030_, v___x_4038_);
v___y_3990_ = v_traceState_4049_;
v___y_3991_ = v_ngen_4047_;
v___y_3992_ = v___y_4040_;
v___y_3993_ = v_nextMacroScope_4046_;
v___y_3994_ = v_auxDeclNGen_4048_;
v___y_3995_ = v___y_4041_;
v___y_3996_ = v_snapshotTasks_4053_;
v___y_3997_ = v_recordedDeps_4050_;
v___y_3998_ = v_messages_4051_;
v___y_3999_ = v_infoState_4052_;
v___y_4000_ = v___x_4055_;
goto v___jp_3989_;
}
else
{
lean_object* v_env_4056_; lean_object* v_nextMacroScope_4057_; lean_object* v_ngen_4058_; lean_object* v_auxDeclNGen_4059_; lean_object* v_traceState_4060_; lean_object* v_recordedDeps_4061_; lean_object* v_messages_4062_; lean_object* v_infoState_4063_; lean_object* v_snapshotTasks_4064_; lean_object* v_asyncMode_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v_env_4056_ = lean_ctor_get(v___x_4042_, 0);
lean_inc_ref(v_env_4056_);
v_nextMacroScope_4057_ = lean_ctor_get(v___x_4042_, 1);
lean_inc(v_nextMacroScope_4057_);
v_ngen_4058_ = lean_ctor_get(v___x_4042_, 2);
lean_inc_ref(v_ngen_4058_);
v_auxDeclNGen_4059_ = lean_ctor_get(v___x_4042_, 3);
lean_inc_ref(v_auxDeclNGen_4059_);
v_traceState_4060_ = lean_ctor_get(v___x_4042_, 4);
lean_inc_ref(v_traceState_4060_);
v_recordedDeps_4061_ = lean_ctor_get(v___x_4042_, 6);
lean_inc_ref(v_recordedDeps_4061_);
v_messages_4062_ = lean_ctor_get(v___x_4042_, 7);
lean_inc_ref(v_messages_4062_);
v_infoState_4063_ = lean_ctor_get(v___x_4042_, 8);
lean_inc_ref(v_infoState_4063_);
v_snapshotTasks_4064_ = lean_ctor_get(v___x_4042_, 9);
lean_inc_ref(v_snapshotTasks_4064_);
lean_dec(v___x_4042_);
v_asyncMode_4065_ = lean_ctor_get(v_toEnvExtension_4043_, 2);
lean_inc_ref_n(v_toEnvExtension_4043_, 2);
v___x_4066_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4043_, v_env_4056_);
lean_dec_ref(v_env_4056_);
v___x_4067_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4043_, v___x_4066_, v___f_4037_, v_asyncMode_4065_, v___x_4030_, v___x_4038_);
v___y_3990_ = v_traceState_4060_;
v___y_3991_ = v_ngen_4058_;
v___y_3992_ = v___y_4040_;
v___y_3993_ = v_nextMacroScope_4057_;
v___y_3994_ = v_auxDeclNGen_4059_;
v___y_3995_ = v___y_4041_;
v___y_3996_ = v_snapshotTasks_4064_;
v___y_3997_ = v_recordedDeps_4061_;
v___y_3998_ = v_messages_4062_;
v___y_3999_ = v_infoState_4063_;
v___y_4000_ = v___x_4067_;
goto v___jp_3989_;
}
}
}
else
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
lean_dec_ref_known(v_entry_4025_, 1);
lean_dec(v_hint_3983_);
lean_dec(v_mod_3981_);
v___x_4101_ = lean_box(0);
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
return v___x_4102_;
}
v___jp_3989_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v_mctx_4005_; lean_object* v_zetaDeltaFVarIds_4006_; lean_object* v_postponed_4007_; lean_object* v_diag_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4019_; 
v___x_4001_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
v___x_4002_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4002_, 0, v___y_4000_);
lean_ctor_set(v___x_4002_, 1, v___y_3993_);
lean_ctor_set(v___x_4002_, 2, v___y_3991_);
lean_ctor_set(v___x_4002_, 3, v___y_3994_);
lean_ctor_set(v___x_4002_, 4, v___y_3990_);
lean_ctor_set(v___x_4002_, 5, v___x_4001_);
lean_ctor_set(v___x_4002_, 6, v___y_3997_);
lean_ctor_set(v___x_4002_, 7, v___y_3998_);
lean_ctor_set(v___x_4002_, 8, v___y_3999_);
lean_ctor_set(v___x_4002_, 9, v___y_3996_);
v___x_4003_ = lean_st_ref_put(v___y_3995_, v___x_4002_);
v___x_4004_ = lean_st_ref_take(v___y_3992_);
v_mctx_4005_ = lean_ctor_get(v___x_4004_, 0);
v_zetaDeltaFVarIds_4006_ = lean_ctor_get(v___x_4004_, 2);
v_postponed_4007_ = lean_ctor_get(v___x_4004_, 3);
v_diag_4008_ = lean_ctor_get(v___x_4004_, 4);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4019_ == 0)
{
lean_object* v_unused_4020_; 
v_unused_4020_ = lean_ctor_get(v___x_4004_, 1);
lean_dec(v_unused_4020_);
v___x_4010_ = v___x_4004_;
v_isShared_4011_ = v_isSharedCheck_4019_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_diag_4008_);
lean_inc(v_postponed_4007_);
lean_inc(v_zetaDeltaFVarIds_4006_);
lean_inc(v_mctx_4005_);
lean_dec(v___x_4004_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4019_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4015_; 
v___x_4012_ = lean_box(0);
v___x_4013_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__5);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 1, v___x_4013_);
v___x_4015_ = v___x_4010_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_mctx_4005_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v___x_4013_);
lean_ctor_set(v_reuseFailAlloc_4018_, 2, v_zetaDeltaFVarIds_4006_);
lean_ctor_set(v_reuseFailAlloc_4018_, 3, v_postponed_4007_);
lean_ctor_set(v_reuseFailAlloc_4018_, 4, v_diag_4008_);
v___x_4015_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_st_ref_put(v___y_3992_, v___x_4015_);
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4012_);
return v___x_4017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___boxed(lean_object* v_mod_4103_, lean_object* v_isMeta_4104_, lean_object* v_hint_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
uint8_t v_isMeta_boxed_4111_; lean_object* v_res_4112_; 
v_isMeta_boxed_4111_ = lean_unbox(v_isMeta_4104_);
v_res_4112_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_mod_4103_, v_isMeta_boxed_4111_, v_hint_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(lean_object* v_a_4113_, lean_object* v_x_4114_){
_start:
{
if (lean_obj_tag(v_x_4114_) == 0)
{
lean_object* v___x_4115_; 
v___x_4115_ = lean_box(0);
return v___x_4115_;
}
else
{
lean_object* v_key_4116_; lean_object* v_value_4117_; lean_object* v_tail_4118_; uint8_t v___x_4119_; 
v_key_4116_ = lean_ctor_get(v_x_4114_, 0);
v_value_4117_ = lean_ctor_get(v_x_4114_, 1);
v_tail_4118_ = lean_ctor_get(v_x_4114_, 2);
v___x_4119_ = lean_name_eq(v_key_4116_, v_a_4113_);
if (v___x_4119_ == 0)
{
v_x_4114_ = v_tail_4118_;
goto _start;
}
else
{
lean_object* v___x_4121_; 
lean_inc(v_value_4117_);
v___x_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4121_, 0, v_value_4117_);
return v___x_4121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_4122_, lean_object* v_x_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4122_, v_x_4123_);
lean_dec(v_x_4123_);
lean_dec(v_a_4122_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(lean_object* v_m_4125_, lean_object* v_a_4126_){
_start:
{
lean_object* v_buckets_4127_; lean_object* v___x_4128_; uint64_t v___y_4130_; 
v_buckets_4127_ = lean_ctor_get(v_m_4125_, 1);
v___x_4128_ = lean_array_get_size(v_buckets_4127_);
if (lean_obj_tag(v_a_4126_) == 0)
{
uint64_t v___x_4144_; 
v___x_4144_ = 1723ULL;
v___y_4130_ = v___x_4144_;
goto v___jp_4129_;
}
else
{
uint64_t v_hash_4145_; 
v_hash_4145_ = lean_ctor_get_uint64(v_a_4126_, sizeof(void*)*2);
v___y_4130_ = v_hash_4145_;
goto v___jp_4129_;
}
v___jp_4129_:
{
uint64_t v___x_4131_; uint64_t v___x_4132_; uint64_t v_fold_4133_; uint64_t v___x_4134_; uint64_t v___x_4135_; uint64_t v___x_4136_; size_t v___x_4137_; size_t v___x_4138_; size_t v___x_4139_; size_t v___x_4140_; size_t v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4131_ = 32ULL;
v___x_4132_ = lean_uint64_shift_right(v___y_4130_, v___x_4131_);
v_fold_4133_ = lean_uint64_xor(v___y_4130_, v___x_4132_);
v___x_4134_ = 16ULL;
v___x_4135_ = lean_uint64_shift_right(v_fold_4133_, v___x_4134_);
v___x_4136_ = lean_uint64_xor(v_fold_4133_, v___x_4135_);
v___x_4137_ = lean_uint64_to_usize(v___x_4136_);
v___x_4138_ = lean_usize_of_nat(v___x_4128_);
v___x_4139_ = ((size_t)1ULL);
v___x_4140_ = lean_usize_sub(v___x_4138_, v___x_4139_);
v___x_4141_ = lean_usize_land(v___x_4137_, v___x_4140_);
v___x_4142_ = lean_array_uget_borrowed(v_buckets_4127_, v___x_4141_);
v___x_4143_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4126_, v___x_4142_);
return v___x_4143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg___boxed(lean_object* v_m_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v_m_4146_, v_a_4147_);
lean_dec(v_a_4147_);
lean_dec_ref(v_m_4146_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v___x_4149_, lean_object* v_declName_4150_, lean_object* v_as_4151_, size_t v_sz_4152_, size_t v_i_4153_, lean_object* v_b_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
uint8_t v___x_4160_; 
v___x_4160_ = lean_usize_dec_lt(v_i_4153_, v_sz_4152_);
if (v___x_4160_ == 0)
{
lean_object* v___x_4161_; 
lean_dec(v_declName_4150_);
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v_b_4154_);
return v___x_4161_;
}
else
{
lean_object* v___x_4162_; lean_object* v_modules_4163_; lean_object* v___x_4164_; lean_object* v_a_4165_; lean_object* v___x_4166_; lean_object* v_toImport_4167_; lean_object* v_module_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; lean_object* v___x_4171_; 
v___x_4162_ = l_Lean_Environment_header(v___x_4149_);
v_modules_4163_ = lean_ctor_get(v___x_4162_, 3);
lean_inc_ref(v_modules_4163_);
lean_dec_ref(v___x_4162_);
v___x_4164_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4165_ = lean_array_uget_borrowed(v_as_4151_, v_i_4153_);
v___x_4166_ = lean_array_get(v___x_4164_, v_modules_4163_, v_a_4165_);
lean_dec_ref(v_modules_4163_);
v_toImport_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc_ref(v_toImport_4167_);
lean_dec(v___x_4166_);
v_module_4168_ = lean_ctor_get(v_toImport_4167_, 0);
lean_inc(v_module_4168_);
lean_dec_ref(v_toImport_4167_);
v___x_4169_ = lean_box(0);
v___x_4170_ = 0;
lean_inc(v_declName_4150_);
v___x_4171_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_module_4168_, v___x_4170_, v_declName_4150_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
if (lean_obj_tag(v___x_4171_) == 0)
{
size_t v___x_4172_; size_t v___x_4173_; 
lean_dec_ref_known(v___x_4171_, 1);
v___x_4172_ = ((size_t)1ULL);
v___x_4173_ = lean_usize_add(v_i_4153_, v___x_4172_);
v_i_4153_ = v___x_4173_;
v_b_4154_ = v___x_4169_;
goto _start;
}
else
{
lean_dec(v_declName_4150_);
return v___x_4171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v___x_4175_, lean_object* v_declName_4176_, lean_object* v_as_4177_, lean_object* v_sz_4178_, lean_object* v_i_4179_, lean_object* v_b_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
size_t v_sz_boxed_4186_; size_t v_i_boxed_4187_; lean_object* v_res_4188_; 
v_sz_boxed_4186_ = lean_unbox_usize(v_sz_4178_);
lean_dec(v_sz_4178_);
v_i_boxed_4187_ = lean_unbox_usize(v_i_4179_);
lean_dec(v_i_4179_);
v_res_4188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v___x_4175_, v_declName_4176_, v_as_4177_, v_sz_boxed_4186_, v_i_boxed_4187_, v_b_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec_ref(v_as_4177_);
lean_dec_ref(v___x_4175_);
return v_res_4188_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = l_Std_HashMap_instInhabited___redArg();
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_4192_, uint8_t v_isMeta_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v_env_4204_; lean_object* v___y_4206_; lean_object* v___x_4219_; 
v___x_4199_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_4200_ = lean_st_ref_get(v___y_4197_);
v_env_4204_ = lean_ctor_get(v___x_4200_, 0);
lean_inc_ref(v_env_4204_);
lean_dec(v___x_4200_);
v___x_4219_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4204_, v_declName_4192_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_dec_ref(v_env_4204_);
lean_dec(v_declName_4192_);
goto v___jp_4201_;
}
else
{
lean_object* v_val_4220_; lean_object* v___x_4221_; lean_object* v_modules_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; 
v_val_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_val_4220_);
lean_dec_ref_known(v___x_4219_, 1);
v___x_4221_ = l_Lean_Environment_header(v_env_4204_);
v_modules_4222_ = lean_ctor_get(v___x_4221_, 3);
lean_inc_ref(v_modules_4222_);
lean_dec_ref(v___x_4221_);
v___x_4223_ = lean_array_get_size(v_modules_4222_);
v___x_4224_ = lean_nat_dec_lt(v_val_4220_, v___x_4223_);
if (v___x_4224_ == 0)
{
lean_dec_ref(v_modules_4222_);
lean_dec(v_val_4220_);
lean_dec_ref(v_env_4204_);
lean_dec(v_declName_4192_);
goto v___jp_4201_;
}
else
{
lean_object* v___x_4225_; lean_object* v___x_4226_; uint8_t v___y_4228_; 
v___x_4225_ = lean_array_fget(v_modules_4222_, v_val_4220_);
lean_dec(v_val_4220_);
lean_dec_ref(v_modules_4222_);
v___x_4226_ = lean_st_ref_get(v___y_4197_);
if (v_isMeta_4193_ == 0)
{
lean_dec(v___x_4226_);
v___y_4228_ = v_isMeta_4193_;
goto v___jp_4227_;
}
else
{
lean_object* v_env_4239_; uint8_t v___x_4240_; 
v_env_4239_ = lean_ctor_get(v___x_4226_, 0);
lean_inc_ref(v_env_4239_);
lean_dec(v___x_4226_);
lean_inc(v_declName_4192_);
v___x_4240_ = l_Lean_isMarkedMeta(v_env_4239_, v_declName_4192_);
if (v___x_4240_ == 0)
{
v___y_4228_ = v_isMeta_4193_;
goto v___jp_4227_;
}
else
{
uint8_t v___x_4241_; 
v___x_4241_ = 0;
v___y_4228_ = v___x_4241_;
goto v___jp_4227_;
}
}
v___jp_4227_:
{
lean_object* v_toImport_4229_; lean_object* v_module_4230_; lean_object* v___x_4231_; 
v_toImport_4229_ = lean_ctor_get(v___x_4225_, 0);
lean_inc_ref(v_toImport_4229_);
lean_dec(v___x_4225_);
v_module_4230_ = lean_ctor_get(v_toImport_4229_, 0);
lean_inc(v_module_4230_);
lean_dec_ref(v_toImport_4229_);
lean_inc(v_declName_4192_);
v___x_4231_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_module_4230_, v___y_4228_, v_declName_4192_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
lean_dec_ref_known(v___x_4231_, 1);
v___x_4232_ = l_Lean_indirectModUseExt;
v___x_4233_ = lean_box(1);
v___x_4234_ = lean_box(0);
lean_inc_ref(v_env_4204_);
v___x_4235_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4199_, v___x_4232_, v_env_4204_, v___x_4233_, v___x_4234_);
v___x_4236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4235_, v_declName_4192_);
lean_dec(v___x_4235_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v___x_4237_; 
v___x_4237_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_4206_ = v___x_4237_;
goto v___jp_4205_;
}
else
{
lean_object* v_val_4238_; 
v_val_4238_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_val_4238_);
lean_dec_ref_known(v___x_4236_, 1);
v___y_4206_ = v_val_4238_;
goto v___jp_4205_;
}
}
else
{
lean_dec_ref(v_env_4204_);
lean_dec(v_declName_4192_);
return v___x_4231_;
}
}
}
}
v___jp_4201_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = lean_box(0);
v___x_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
return v___x_4203_;
}
v___jp_4205_:
{
lean_object* v___x_4207_; size_t v_sz_4208_; size_t v___x_4209_; lean_object* v___x_4210_; 
v___x_4207_ = lean_box(0);
v_sz_4208_ = lean_array_size(v___y_4206_);
v___x_4209_ = ((size_t)0ULL);
v___x_4210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_env_4204_, v_declName_4192_, v___y_4206_, v_sz_4208_, v___x_4209_, v___x_4207_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
lean_dec_ref(v___y_4206_);
lean_dec_ref(v_env_4204_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4217_ == 0)
{
lean_object* v_unused_4218_; 
v_unused_4218_ = lean_ctor_get(v___x_4210_, 0);
lean_dec(v_unused_4218_);
v___x_4212_ = v___x_4210_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_dec(v___x_4210_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v___x_4207_);
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4207_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
else
{
return v___x_4210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_4242_, lean_object* v_isMeta_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
uint8_t v_isMeta_boxed_4249_; lean_object* v_res_4250_; 
v_isMeta_boxed_4249_ = lean_unbox(v_isMeta_4243_);
v_res_4250_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_4242_, v_isMeta_boxed_4249_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_4251_, uint8_t v_when_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
if (v_when_4252_ == 0)
{
lean_object* v___x_4258_; 
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
lean_inc(v___y_4254_);
lean_inc_ref(v___y_4253_);
v___x_4258_ = lean_apply_5(v_x_4251_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, lean_box(0));
return v___x_4258_;
}
else
{
uint8_t v___x_4259_; lean_object* v___x_4260_; 
v___x_4259_ = 0;
v___x_4260_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_4251_, v___x_4259_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
return v___x_4260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_4261_, lean_object* v_when_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
uint8_t v_when_boxed_4268_; lean_object* v_res_4269_; 
v_when_boxed_4268_ = lean_unbox(v_when_4262_);
v_res_4269_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_4261_, v_when_boxed_4268_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v_ext_4270_, uint8_t v_showInfo_4271_, uint8_t v_minIndexable_4272_, lean_object* v_attrName_4273_, lean_object* v___x_4274_, lean_object* v_declName_4275_, lean_object* v_stx_4276_, uint8_t v_attrKind_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
uint8_t v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___f_4286_; uint8_t v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4281_ = 0;
v___x_4282_ = lean_box(v_attrKind_4277_);
v___x_4283_ = lean_box(v_showInfo_4271_);
v___x_4284_ = lean_box(v_minIndexable_4272_);
v___x_4285_ = lean_box(v___x_4281_);
lean_inc(v_declName_4275_);
v___f_4286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_4286_, 0, v_declName_4275_);
lean_closure_set(v___f_4286_, 1, v___x_4282_);
lean_closure_set(v___f_4286_, 2, v_stx_4276_);
lean_closure_set(v___f_4286_, 3, v_ext_4270_);
lean_closure_set(v___f_4286_, 4, v___x_4283_);
lean_closure_set(v___f_4286_, 5, v___x_4284_);
lean_closure_set(v___f_4286_, 6, v___x_4285_);
lean_closure_set(v___f_4286_, 7, v_attrName_4273_);
v___x_4287_ = 1;
v___x_4288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_4289_ = lean_unsigned_to_nat(32u);
v___x_4290_ = lean_mk_empty_array_with_capacity(v___x_4289_);
lean_dec_ref(v___x_4290_);
v___x_4291_ = lean_unsigned_to_nat(0u);
v___x_4292_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_4293_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_4294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_4295_ = lean_box(0);
lean_inc(v___x_4274_);
v___x_4296_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4296_, 0, v___x_4288_);
lean_ctor_set(v___x_4296_, 1, v___x_4274_);
lean_ctor_set(v___x_4296_, 2, v___x_4293_);
lean_ctor_set(v___x_4296_, 3, v___x_4294_);
lean_ctor_set(v___x_4296_, 4, v___x_4295_);
lean_ctor_set(v___x_4296_, 5, v___x_4291_);
lean_ctor_set(v___x_4296_, 6, v___x_4295_);
lean_ctor_set_uint8(v___x_4296_, sizeof(void*)*7, v___x_4281_);
lean_ctor_set_uint8(v___x_4296_, sizeof(void*)*7 + 1, v___x_4281_);
lean_ctor_set_uint8(v___x_4296_, sizeof(void*)*7 + 2, v___x_4281_);
lean_ctor_set_uint8(v___x_4296_, sizeof(void*)*7 + 3, v___x_4287_);
v___x_4297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_4298_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_4299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_4300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4297_);
lean_ctor_set(v___x_4300_, 1, v___x_4298_);
lean_ctor_set(v___x_4300_, 2, v___x_4274_);
lean_ctor_set(v___x_4300_, 3, v___x_4292_);
lean_ctor_set(v___x_4300_, 4, v___x_4299_);
v___x_4301_ = lean_st_mk_ref(v___x_4300_);
v___x_4302_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_4275_, v___x_4281_, v___x_4296_, v___x_4301_, v___y_4278_, v___y_4279_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v___x_4303_; 
lean_dec_ref_known(v___x_4302_, 1);
v___x_4303_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_4286_, v___x_4287_, v___x_4296_, v___x_4301_, v___y_4278_, v___y_4279_);
lean_dec_ref_known(v___x_4296_, 7);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4312_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4306_ = v___x_4303_;
v_isShared_4307_ = v_isSharedCheck_4312_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4303_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4312_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4308_; lean_object* v___x_4310_; 
v___x_4308_ = lean_st_ref_get(v___x_4301_);
lean_dec(v___x_4301_);
lean_dec(v___x_4308_);
if (v_isShared_4307_ == 0)
{
v___x_4310_ = v___x_4306_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4304_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
else
{
lean_dec(v___x_4301_);
return v___x_4303_;
}
}
else
{
lean_dec(v___x_4301_);
lean_dec_ref_known(v___x_4296_, 7);
lean_dec_ref(v___f_4286_);
return v___x_4302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v_ext_4313_, lean_object* v_showInfo_4314_, lean_object* v_minIndexable_4315_, lean_object* v_attrName_4316_, lean_object* v___x_4317_, lean_object* v_declName_4318_, lean_object* v_stx_4319_, lean_object* v_attrKind_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
uint8_t v_showInfo_boxed_4324_; uint8_t v_minIndexable_boxed_4325_; uint8_t v_attrKind_boxed_4326_; lean_object* v_res_4327_; 
v_showInfo_boxed_4324_ = lean_unbox(v_showInfo_4314_);
v_minIndexable_boxed_4325_ = lean_unbox(v_minIndexable_4315_);
v_attrKind_boxed_4326_ = lean_unbox(v_attrKind_4320_);
v_res_4327_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v_ext_4313_, v_showInfo_boxed_4324_, v_minIndexable_boxed_4325_, v_attrName_4316_, v___x_4317_, v_declName_4318_, v_stx_4319_, v_attrKind_boxed_4326_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_4350_, uint8_t v_minIndexable_4351_, uint8_t v_showInfo_4352_, lean_object* v_ext_4353_, lean_object* v_ref_4354_){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___f_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___f_4361_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4407_; 
v___x_4356_ = lean_box(1);
v___x_4357_ = lean_box(v_showInfo_4352_);
lean_inc_n(v_attrName_4350_, 2);
lean_inc_ref(v_ext_4353_);
v___f_4358_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_4358_, 0, v_ext_4353_);
lean_closure_set(v___f_4358_, 1, v___x_4356_);
lean_closure_set(v___f_4358_, 2, v___x_4357_);
lean_closure_set(v___f_4358_, 3, v_attrName_4350_);
v___x_4359_ = lean_box(v_showInfo_4352_);
v___x_4360_ = lean_box(v_minIndexable_4351_);
v___f_4361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_4361_, 0, v_ext_4353_);
lean_closure_set(v___f_4361_, 1, v___x_4359_);
lean_closure_set(v___f_4361_, 2, v___x_4360_);
lean_closure_set(v___f_4361_, 3, v_attrName_4350_);
lean_closure_set(v___f_4361_, 4, v___x_4356_);
if (v_minIndexable_4351_ == 0)
{
if (v_showInfo_4352_ == 0)
{
lean_inc(v_attrName_4350_);
v___y_4407_ = v_attrName_4350_;
goto v___jp_4406_;
}
else
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_4350_);
v___x_4437_ = lean_name_append_after(v_attrName_4350_, v___x_4436_);
v___y_4407_ = v___x_4437_;
goto v___jp_4406_;
}
}
else
{
if (v_showInfo_4352_ == 0)
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_4350_);
v___x_4439_ = lean_name_append_after(v_attrName_4350_, v___x_4438_);
v___y_4407_ = v___x_4439_;
goto v___jp_4406_;
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_4350_);
v___x_4441_ = lean_name_append_after(v_attrName_4350_, v___x_4440_);
v___y_4407_ = v___x_4441_;
goto v___jp_4406_;
}
}
v___jp_4362_:
{
lean_object* v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; uint8_t v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_4366_ = 1;
v___x_4367_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4350_, v___x_4366_);
v___x_4368_ = lean_string_append(v___x_4365_, v___x_4367_);
v___x_4369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_4370_ = lean_string_append(v___x_4368_, v___x_4369_);
v___x_4371_ = lean_string_append(v___x_4370_, v___x_4367_);
v___x_4372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_4373_ = lean_string_append(v___x_4371_, v___x_4372_);
v___x_4374_ = lean_string_append(v___x_4373_, v___x_4367_);
v___x_4375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_4376_ = lean_string_append(v___x_4374_, v___x_4375_);
v___x_4377_ = lean_string_append(v___x_4376_, v___x_4367_);
v___x_4378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_4379_ = lean_string_append(v___x_4377_, v___x_4378_);
v___x_4380_ = lean_string_append(v___x_4379_, v___x_4367_);
v___x_4381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_4382_ = lean_string_append(v___x_4380_, v___x_4381_);
v___x_4383_ = lean_string_append(v___x_4382_, v___x_4367_);
v___x_4384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_4385_ = lean_string_append(v___x_4383_, v___x_4384_);
v___x_4386_ = lean_string_append(v___x_4385_, v___x_4367_);
v___x_4387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_4388_ = lean_string_append(v___x_4386_, v___x_4387_);
v___x_4389_ = lean_string_append(v___x_4388_, v___x_4367_);
v___x_4390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_4391_ = lean_string_append(v___x_4389_, v___x_4390_);
v___x_4392_ = lean_string_append(v___x_4391_, v___x_4367_);
v___x_4393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_4394_ = lean_string_append(v___x_4392_, v___x_4393_);
v___x_4395_ = lean_string_append(v___x_4394_, v___x_4367_);
v___x_4396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_4397_ = lean_string_append(v___x_4395_, v___x_4396_);
v___x_4398_ = lean_string_append(v___x_4397_, v___x_4367_);
lean_dec_ref(v___x_4367_);
v___x_4399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_4400_ = lean_string_append(v___x_4398_, v___x_4399_);
v___x_4401_ = lean_string_append(v___y_4364_, v___x_4400_);
lean_dec_ref(v___x_4400_);
v___x_4402_ = 1;
v___x_4403_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4403_, 0, v_ref_4354_);
lean_ctor_set(v___x_4403_, 1, v___y_4363_);
lean_ctor_set(v___x_4403_, 2, v___x_4401_);
lean_ctor_set_uint8(v___x_4403_, sizeof(void*)*3, v___x_4402_);
v___x_4404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
lean_ctor_set(v___x_4404_, 1, v___f_4361_);
lean_ctor_set(v___x_4404_, 2, v___f_4358_);
v___x_4405_ = l_Lean_registerBuiltinAttribute(v___x_4404_);
return v___x_4405_;
}
v___jp_4406_:
{
lean_object* v___x_4408_; 
lean_inc(v___y_4407_);
v___x_4408_ = l_Lean_registerAutomationAttr(v___y_4407_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_dec_ref_known(v___x_4408_, 1);
if (v_minIndexable_4351_ == 0)
{
if (v_showInfo_4352_ == 0)
{
lean_object* v___x_4409_; uint8_t v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_4410_ = 1;
lean_inc(v_attrName_4350_);
v___x_4411_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4350_, v___x_4410_);
v___x_4412_ = lean_string_append(v___x_4409_, v___x_4411_);
lean_dec_ref(v___x_4411_);
v___x_4413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_4414_ = lean_string_append(v___x_4412_, v___x_4413_);
v___y_4363_ = v___y_4407_;
v___y_4364_ = v___x_4414_;
goto v___jp_4362_;
}
else
{
lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4350_);
v___x_4416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4350_, v_showInfo_4352_);
v___x_4417_ = lean_string_append(v___x_4415_, v___x_4416_);
v___x_4418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_4419_ = lean_string_append(v___x_4417_, v___x_4418_);
v___x_4420_ = lean_string_append(v___x_4419_, v___x_4416_);
lean_dec_ref(v___x_4416_);
v___x_4421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_4422_ = lean_string_append(v___x_4420_, v___x_4421_);
v___y_4363_ = v___y_4407_;
v___y_4364_ = v___x_4422_;
goto v___jp_4362_;
}
}
else
{
if (v_showInfo_4352_ == 0)
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4350_);
v___x_4424_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4350_, v_minIndexable_4351_);
v___x_4425_ = lean_string_append(v___x_4423_, v___x_4424_);
lean_dec_ref(v___x_4424_);
v___x_4426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_4427_ = lean_string_append(v___x_4425_, v___x_4426_);
v___y_4363_ = v___y_4407_;
v___y_4364_ = v___x_4427_;
goto v___jp_4362_;
}
else
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4350_);
v___x_4429_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4350_, v_showInfo_4352_);
v___x_4430_ = lean_string_append(v___x_4428_, v___x_4429_);
v___x_4431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_4432_ = lean_string_append(v___x_4430_, v___x_4431_);
v___x_4433_ = lean_string_append(v___x_4432_, v___x_4429_);
lean_dec_ref(v___x_4429_);
v___x_4434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_4435_ = lean_string_append(v___x_4433_, v___x_4434_);
v___y_4363_ = v___y_4407_;
v___y_4364_ = v___x_4435_;
goto v___jp_4362_;
}
}
}
else
{
lean_dec(v___y_4407_);
lean_dec_ref(v___f_4361_);
lean_dec_ref(v___f_4358_);
lean_dec(v_ref_4354_);
lean_dec(v_attrName_4350_);
return v___x_4408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_4442_, lean_object* v_minIndexable_4443_, lean_object* v_showInfo_4444_, lean_object* v_ext_4445_, lean_object* v_ref_4446_, lean_object* v_a_4447_){
_start:
{
uint8_t v_minIndexable_boxed_4448_; uint8_t v_showInfo_boxed_4449_; lean_object* v_res_4450_; 
v_minIndexable_boxed_4448_ = lean_unbox(v_minIndexable_4443_);
v_showInfo_boxed_4449_ = lean_unbox(v_showInfo_4444_);
v_res_4450_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4442_, v_minIndexable_boxed_4448_, v_showInfo_boxed_4449_, v_ext_4445_, v_ref_4446_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_4451_, lean_object* v_msg_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_4459_, lean_object* v_msg_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_4459_, v_msg_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_4467_, uint8_t v_attrKind_4468_, uint8_t v_showInfo_4469_, uint8_t v_minIndexable_4470_, lean_object* v_as_4471_, lean_object* v_as_x27_4472_, lean_object* v_b_4473_, lean_object* v_a_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_4467_, v_attrKind_4468_, v_showInfo_4469_, v_minIndexable_4470_, v_as_x27_4472_, v_b_4473_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_4481_, lean_object* v_attrKind_4482_, lean_object* v_showInfo_4483_, lean_object* v_minIndexable_4484_, lean_object* v_as_4485_, lean_object* v_as_x27_4486_, lean_object* v_b_4487_, lean_object* v_a_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
uint8_t v_attrKind_boxed_4494_; uint8_t v_showInfo_boxed_4495_; uint8_t v_minIndexable_boxed_4496_; lean_object* v_res_4497_; 
v_attrKind_boxed_4494_ = lean_unbox(v_attrKind_4482_);
v_showInfo_boxed_4495_ = lean_unbox(v_showInfo_4483_);
v_minIndexable_boxed_4496_ = lean_unbox(v_minIndexable_4484_);
v_res_4497_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_4481_, v_attrKind_boxed_4494_, v_showInfo_boxed_4495_, v_minIndexable_boxed_4496_, v_as_4485_, v_as_x27_4486_, v_b_4487_, v_a_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v_as_x27_4486_);
lean_dec(v_as_4485_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_4498_, lean_object* v_x_4499_, uint8_t v_when_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v___x_4506_; 
v___x_4506_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_4499_, v_when_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_4507_, lean_object* v_x_4508_, lean_object* v_when_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
uint8_t v_when_boxed_4515_; lean_object* v_res_4516_; 
v_when_boxed_4515_ = lean_unbox(v_when_4509_);
v_res_4516_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_4507_, v_x_4508_, v_when_boxed_4515_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v_00_u03b2_4517_, lean_object* v_m_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v___x_4520_; 
v___x_4520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v_m_4518_, v_a_4519_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4521_, lean_object* v_m_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_00_u03b2_4521_, v_m_4522_, v_a_4523_);
lean_dec(v_a_4523_);
lean_dec_ref(v_m_4522_);
return v_res_4524_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_4525_, lean_object* v_x_4526_, lean_object* v_x_4527_){
_start:
{
uint8_t v___x_4528_; 
v___x_4528_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v_x_4526_, v_x_4527_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4529_, lean_object* v_x_4530_, lean_object* v_x_4531_){
_start:
{
uint8_t v_res_4532_; lean_object* v_r_4533_; 
v_res_4532_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(v_00_u03b2_4529_, v_x_4530_, v_x_4531_);
lean_dec_ref(v_x_4531_);
lean_dec_ref(v_x_4530_);
v_r_4533_ = lean_box(v_res_4532_);
return v_r_4533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4534_, lean_object* v_a_4535_, lean_object* v_x_4536_){
_start:
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4535_, v_x_4536_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4538_, lean_object* v_a_4539_, lean_object* v_x_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(v_00_u03b2_4538_, v_a_4539_, v_x_4540_);
lean_dec(v_x_4540_);
lean_dec(v_a_4539_);
return v_res_4541_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4542_, lean_object* v_x_4543_, size_t v_x_4544_, lean_object* v_x_4545_){
_start:
{
uint8_t v___x_4546_; 
v___x_4546_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_4543_, v_x_4544_, v_x_4545_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4547_, lean_object* v_x_4548_, lean_object* v_x_4549_, lean_object* v_x_4550_){
_start:
{
size_t v_x_13734__boxed_4551_; uint8_t v_res_4552_; lean_object* v_r_4553_; 
v_x_13734__boxed_4551_ = lean_unbox_usize(v_x_4549_);
lean_dec(v_x_4549_);
v_res_4552_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(v_00_u03b2_4547_, v_x_4548_, v_x_13734__boxed_4551_, v_x_4550_);
lean_dec_ref(v_x_4550_);
lean_dec_ref(v_x_4548_);
v_r_4553_ = lean_box(v_res_4552_);
return v_r_4553_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4554_, lean_object* v_keys_4555_, lean_object* v_vals_4556_, lean_object* v_heq_4557_, lean_object* v_i_4558_, lean_object* v_k_4559_){
_start:
{
uint8_t v___x_4560_; 
v___x_4560_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_keys_4555_, v_i_4558_, v_k_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_4561_, lean_object* v_keys_4562_, lean_object* v_vals_4563_, lean_object* v_heq_4564_, lean_object* v_i_4565_, lean_object* v_k_4566_){
_start:
{
uint8_t v_res_4567_; lean_object* v_r_4568_; 
v_res_4567_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(v_00_u03b2_4561_, v_keys_4562_, v_vals_4563_, v_heq_4564_, v_i_4565_, v_k_4566_);
lean_dec_ref(v_k_4566_);
lean_dec_ref(v_vals_4563_);
lean_dec_ref(v_keys_4562_);
v_r_4568_ = lean_box(v_res_4567_);
return v_r_4568_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4569_ = lean_box(0);
v___x_4570_ = lean_unsigned_to_nat(16u);
v___x_4571_ = lean_mk_array(v___x_4570_, v___x_4569_);
return v___x_4571_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4572_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_4573_ = lean_unsigned_to_nat(0u);
v___x_4574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4573_);
lean_ctor_set(v___x_4574_, 1, v___x_4572_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_4577_ = lean_st_mk_ref(v___x_4576_);
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_4581_, lean_object* v_msg_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v_ref_4586_; lean_object* v___x_4587_; lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4633_; 
v_ref_4586_ = lean_ctor_get(v___y_4583_, 2);
v___x_4587_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_4582_, v___y_4583_, v___y_4584_);
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4590_ = v___x_4587_;
v_isShared_4591_ = v_isSharedCheck_4633_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4587_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4633_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4592_; lean_object* v_traceState_4593_; lean_object* v_env_4594_; lean_object* v_nextMacroScope_4595_; lean_object* v_ngen_4596_; lean_object* v_auxDeclNGen_4597_; lean_object* v_cache_4598_; lean_object* v_recordedDeps_4599_; lean_object* v_messages_4600_; lean_object* v_infoState_4601_; lean_object* v_snapshotTasks_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4632_; 
v___x_4592_ = lean_st_ref_take(v___y_4584_);
v_traceState_4593_ = lean_ctor_get(v___x_4592_, 4);
v_env_4594_ = lean_ctor_get(v___x_4592_, 0);
v_nextMacroScope_4595_ = lean_ctor_get(v___x_4592_, 1);
v_ngen_4596_ = lean_ctor_get(v___x_4592_, 2);
v_auxDeclNGen_4597_ = lean_ctor_get(v___x_4592_, 3);
v_cache_4598_ = lean_ctor_get(v___x_4592_, 5);
v_recordedDeps_4599_ = lean_ctor_get(v___x_4592_, 6);
v_messages_4600_ = lean_ctor_get(v___x_4592_, 7);
v_infoState_4601_ = lean_ctor_get(v___x_4592_, 8);
v_snapshotTasks_4602_ = lean_ctor_get(v___x_4592_, 9);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4604_ = v___x_4592_;
v_isShared_4605_ = v_isSharedCheck_4632_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_snapshotTasks_4602_);
lean_inc(v_infoState_4601_);
lean_inc(v_messages_4600_);
lean_inc(v_recordedDeps_4599_);
lean_inc(v_cache_4598_);
lean_inc(v_traceState_4593_);
lean_inc(v_auxDeclNGen_4597_);
lean_inc(v_ngen_4596_);
lean_inc(v_nextMacroScope_4595_);
lean_inc(v_env_4594_);
lean_dec(v___x_4592_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4632_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
uint64_t v_tid_4606_; lean_object* v_traces_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4631_; 
v_tid_4606_ = lean_ctor_get_uint64(v_traceState_4593_, sizeof(void*)*1);
v_traces_4607_ = lean_ctor_get(v_traceState_4593_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v_traceState_4593_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4609_ = v_traceState_4593_;
v_isShared_4610_ = v_isSharedCheck_4631_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_traces_4607_);
lean_dec(v_traceState_4593_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4631_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; double v___x_4613_; uint8_t v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
v___x_4611_ = lean_box(0);
v___x_4612_ = lean_box(0);
v___x_4613_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0);
v___x_4614_ = 0;
v___x_4615_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_4616_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4616_, 0, v_cls_4581_);
lean_ctor_set(v___x_4616_, 1, v___x_4612_);
lean_ctor_set(v___x_4616_, 2, v___x_4615_);
lean_ctor_set_float(v___x_4616_, sizeof(void*)*3, v___x_4613_);
lean_ctor_set_float(v___x_4616_, sizeof(void*)*3 + 8, v___x_4613_);
lean_ctor_set_uint8(v___x_4616_, sizeof(void*)*3 + 16, v___x_4614_);
v___x_4617_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2));
v___x_4618_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4616_);
lean_ctor_set(v___x_4618_, 1, v_a_4588_);
lean_ctor_set(v___x_4618_, 2, v___x_4617_);
lean_inc(v_ref_4586_);
v___x_4619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4619_, 0, v_ref_4586_);
lean_ctor_set(v___x_4619_, 1, v___x_4618_);
v___x_4620_ = l_Lean_PersistentArray_push___redArg(v_traces_4607_, v___x_4619_);
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 0, v___x_4620_);
v___x_4622_ = v___x_4609_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4620_);
lean_ctor_set_uint64(v_reuseFailAlloc_4630_, sizeof(void*)*1, v_tid_4606_);
v___x_4622_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
lean_object* v___x_4624_; 
if (v_isShared_4605_ == 0)
{
lean_ctor_set(v___x_4604_, 4, v___x_4622_);
v___x_4624_ = v___x_4604_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_env_4594_);
lean_ctor_set(v_reuseFailAlloc_4629_, 1, v_nextMacroScope_4595_);
lean_ctor_set(v_reuseFailAlloc_4629_, 2, v_ngen_4596_);
lean_ctor_set(v_reuseFailAlloc_4629_, 3, v_auxDeclNGen_4597_);
lean_ctor_set(v_reuseFailAlloc_4629_, 4, v___x_4622_);
lean_ctor_set(v_reuseFailAlloc_4629_, 5, v_cache_4598_);
lean_ctor_set(v_reuseFailAlloc_4629_, 6, v_recordedDeps_4599_);
lean_ctor_set(v_reuseFailAlloc_4629_, 7, v_messages_4600_);
lean_ctor_set(v_reuseFailAlloc_4629_, 8, v_infoState_4601_);
lean_ctor_set(v_reuseFailAlloc_4629_, 9, v_snapshotTasks_4602_);
v___x_4624_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
lean_object* v___x_4625_; lean_object* v___x_4627_; 
v___x_4625_ = lean_st_ref_put(v___y_4584_, v___x_4624_);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 0, v___x_4611_);
v___x_4627_ = v___x_4590_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4611_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_4634_, lean_object* v_msg_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_4634_, v_msg_4635_, v___y_4636_, v___y_4637_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_4640_, uint8_t v_isMeta_4641_, lean_object* v_hint_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v_env_4664_; uint8_t v_isExporting_4665_; lean_object* v_entry_4666_; lean_object* v___x_4667_; lean_object* v_env_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; 
v___x_4662_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0);
v___x_4663_ = lean_st_ref_get(v___y_4644_);
v_env_4664_ = lean_ctor_get(v___x_4663_, 0);
lean_inc_ref(v_env_4664_);
lean_dec(v___x_4663_);
v_isExporting_4665_ = lean_ctor_get_uint8(v_env_4664_, sizeof(void*)*13);
lean_dec_ref(v_env_4664_);
lean_inc(v_mod_4640_);
v_entry_4666_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_4666_, 0, v_mod_4640_);
lean_ctor_set_uint8(v_entry_4666_, sizeof(void*)*1, v_isExporting_4665_);
lean_ctor_set_uint8(v_entry_4666_, sizeof(void*)*1 + 1, v_isMeta_4641_);
v___x_4667_ = lean_st_ref_get(v___y_4644_);
v_env_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc_ref(v_env_4668_);
lean_dec(v___x_4667_);
v___x_4669_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_4670_ = lean_box(1);
v___x_4671_ = lean_box(0);
v___x_4672_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4662_, v___x_4669_, v_env_4668_, v___x_4670_, v___x_4671_);
v___x_4673_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v___x_4672_, v_entry_4666_);
lean_dec(v___x_4672_);
if (v___x_4673_ == 0)
{
lean_object* v_toCold_4674_; lean_object* v_options_4675_; lean_object* v_inheritedTraceOptions_4676_; uint8_t v_hasTrace_4677_; lean_object* v___f_4678_; uint8_t v___x_4679_; lean_object* v___y_4681_; 
v_toCold_4674_ = lean_ctor_get(v___y_4643_, 0);
v_options_4675_ = lean_ctor_get(v_toCold_4674_, 2);
v_inheritedTraceOptions_4676_ = lean_ctor_get(v_toCold_4674_, 11);
v_hasTrace_4677_ = lean_ctor_get_uint8(v_options_4675_, sizeof(void*)*1);
v___f_4678_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_4678_, 0, v___x_4669_);
lean_closure_set(v___f_4678_, 1, v_entry_4666_);
v___x_4679_ = 1;
if (v_hasTrace_4677_ == 0)
{
lean_dec(v_hint_4642_);
lean_dec(v_mod_4640_);
v___y_4681_ = v___y_4644_;
goto v___jp_4680_;
}
else
{
lean_object* v_cls_4699_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4706_; lean_object* v___y_4707_; lean_object* v___x_4719_; uint8_t v___x_4720_; 
v_cls_4699_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_4719_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8);
v___x_4720_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4676_, v_options_4675_, v___x_4719_);
if (v___x_4720_ == 0)
{
lean_dec(v_hint_4642_);
lean_dec(v_mod_4640_);
v___y_4681_ = v___y_4644_;
goto v___jp_4680_;
}
else
{
lean_object* v___x_4721_; lean_object* v___y_4723_; 
v___x_4721_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10);
if (v_isExporting_4665_ == 0)
{
lean_object* v___x_4730_; 
v___x_4730_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15));
v___y_4723_ = v___x_4730_;
goto v___jp_4722_;
}
else
{
lean_object* v___x_4731_; 
v___x_4731_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16));
v___y_4723_ = v___x_4731_;
goto v___jp_4722_;
}
v___jp_4722_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
lean_inc_ref(v___y_4723_);
v___x_4724_ = l_Lean_stringToMessageData(v___y_4723_);
v___x_4725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4721_);
lean_ctor_set(v___x_4725_, 1, v___x_4724_);
v___x_4726_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12);
v___x_4727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4725_);
lean_ctor_set(v___x_4727_, 1, v___x_4726_);
if (v_isMeta_4641_ == 0)
{
lean_object* v___x_4728_; 
v___x_4728_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13));
v___y_4706_ = v___x_4727_;
v___y_4707_ = v___x_4728_;
goto v___jp_4705_;
}
else
{
lean_object* v___x_4729_; 
v___x_4729_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14));
v___y_4706_ = v___x_4727_;
v___y_4707_ = v___x_4729_;
goto v___jp_4705_;
}
}
}
v___jp_4700_:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4703_, 0, v___y_4701_);
lean_ctor_set(v___x_4703_, 1, v___y_4702_);
v___x_4704_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_4699_, v___x_4703_, v___y_4643_, v___y_4644_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_dec_ref_known(v___x_4704_, 1);
v___y_4681_ = v___y_4644_;
goto v___jp_4680_;
}
else
{
lean_dec_ref(v___f_4678_);
return v___x_4704_;
}
}
v___jp_4705_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; 
lean_inc_ref(v___y_4707_);
v___x_4708_ = l_Lean_stringToMessageData(v___y_4707_);
v___x_4709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___y_4706_);
lean_ctor_set(v___x_4709_, 1, v___x_4708_);
v___x_4710_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4);
v___x_4711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4711_, 0, v___x_4709_);
lean_ctor_set(v___x_4711_, 1, v___x_4710_);
v___x_4712_ = l_Lean_MessageData_ofName(v_mod_4640_);
v___x_4713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4711_);
lean_ctor_set(v___x_4713_, 1, v___x_4712_);
v___x_4714_ = l_Lean_Name_isAnonymous(v_hint_4642_);
if (v___x_4714_ == 0)
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4715_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6);
v___x_4716_ = l_Lean_MessageData_ofName(v_hint_4642_);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4715_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___y_4701_ = v___x_4713_;
v___y_4702_ = v___x_4717_;
goto v___jp_4700_;
}
else
{
lean_object* v___x_4718_; 
lean_dec(v_hint_4642_);
v___x_4718_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7);
v___y_4701_ = v___x_4713_;
v___y_4702_ = v___x_4718_;
goto v___jp_4700_;
}
}
}
v___jp_4680_:
{
lean_object* v___x_4682_; lean_object* v_toEnvExtension_4683_; lean_object* v_env_4684_; lean_object* v_nextMacroScope_4685_; lean_object* v_ngen_4686_; lean_object* v_auxDeclNGen_4687_; lean_object* v_traceState_4688_; lean_object* v_recordedDeps_4689_; lean_object* v_messages_4690_; lean_object* v_infoState_4691_; lean_object* v_snapshotTasks_4692_; lean_object* v_asyncMode_4693_; uint8_t v_logWrites_4694_; lean_object* v___x_4695_; 
v___x_4682_ = lean_st_ref_take(v___y_4681_);
v_toEnvExtension_4683_ = lean_ctor_get(v___x_4669_, 0);
v_env_4684_ = lean_ctor_get(v___x_4682_, 0);
lean_inc_ref(v_env_4684_);
v_nextMacroScope_4685_ = lean_ctor_get(v___x_4682_, 1);
lean_inc(v_nextMacroScope_4685_);
v_ngen_4686_ = lean_ctor_get(v___x_4682_, 2);
lean_inc_ref(v_ngen_4686_);
v_auxDeclNGen_4687_ = lean_ctor_get(v___x_4682_, 3);
lean_inc_ref(v_auxDeclNGen_4687_);
v_traceState_4688_ = lean_ctor_get(v___x_4682_, 4);
lean_inc_ref(v_traceState_4688_);
v_recordedDeps_4689_ = lean_ctor_get(v___x_4682_, 6);
lean_inc_ref(v_recordedDeps_4689_);
v_messages_4690_ = lean_ctor_get(v___x_4682_, 7);
lean_inc_ref(v_messages_4690_);
v_infoState_4691_ = lean_ctor_get(v___x_4682_, 8);
lean_inc_ref(v_infoState_4691_);
v_snapshotTasks_4692_ = lean_ctor_get(v___x_4682_, 9);
lean_inc_ref(v_snapshotTasks_4692_);
lean_dec(v___x_4682_);
v_asyncMode_4693_ = lean_ctor_get(v_toEnvExtension_4683_, 2);
v_logWrites_4694_ = lean_ctor_get_uint8(v_toEnvExtension_4683_, sizeof(void*)*6);
v___x_4695_ = lean_box(0);
if (v_logWrites_4694_ == 0)
{
lean_object* v___x_4696_; 
lean_inc_ref(v_toEnvExtension_4683_);
v___x_4696_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4683_, v_env_4684_, v___f_4678_, v_asyncMode_4693_, v___x_4671_, v___x_4679_);
v___y_4647_ = v_infoState_4691_;
v___y_4648_ = v_traceState_4688_;
v___y_4649_ = v_auxDeclNGen_4687_;
v___y_4650_ = v_snapshotTasks_4692_;
v___y_4651_ = v_messages_4690_;
v___y_4652_ = v___y_4681_;
v___y_4653_ = v_recordedDeps_4689_;
v___y_4654_ = v_nextMacroScope_4685_;
v___y_4655_ = v_ngen_4686_;
v___y_4656_ = v___x_4695_;
v___y_4657_ = v___x_4696_;
goto v___jp_4646_;
}
else
{
lean_object* v___x_4697_; lean_object* v___x_4698_; 
lean_inc_ref_n(v_toEnvExtension_4683_, 2);
v___x_4697_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4683_, v_env_4684_);
lean_dec_ref(v_env_4684_);
v___x_4698_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4683_, v___x_4697_, v___f_4678_, v_asyncMode_4693_, v___x_4671_, v___x_4679_);
v___y_4647_ = v_infoState_4691_;
v___y_4648_ = v_traceState_4688_;
v___y_4649_ = v_auxDeclNGen_4687_;
v___y_4650_ = v_snapshotTasks_4692_;
v___y_4651_ = v_messages_4690_;
v___y_4652_ = v___y_4681_;
v___y_4653_ = v_recordedDeps_4689_;
v___y_4654_ = v_nextMacroScope_4685_;
v___y_4655_ = v_ngen_4686_;
v___y_4656_ = v___x_4695_;
v___y_4657_ = v___x_4698_;
goto v___jp_4646_;
}
}
}
else
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
lean_dec_ref_known(v_entry_4666_, 1);
lean_dec(v_hint_4642_);
lean_dec(v_mod_4640_);
v___x_4732_ = lean_box(0);
v___x_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4732_);
return v___x_4733_;
}
v___jp_4646_:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4658_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
v___x_4659_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4659_, 0, v___y_4657_);
lean_ctor_set(v___x_4659_, 1, v___y_4654_);
lean_ctor_set(v___x_4659_, 2, v___y_4655_);
lean_ctor_set(v___x_4659_, 3, v___y_4649_);
lean_ctor_set(v___x_4659_, 4, v___y_4648_);
lean_ctor_set(v___x_4659_, 5, v___x_4658_);
lean_ctor_set(v___x_4659_, 6, v___y_4653_);
lean_ctor_set(v___x_4659_, 7, v___y_4651_);
lean_ctor_set(v___x_4659_, 8, v___y_4647_);
lean_ctor_set(v___x_4659_, 9, v___y_4650_);
v___x_4660_ = lean_st_ref_put(v___y_4652_, v___x_4659_);
v___x_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4661_, 0, v___y_4656_);
return v___x_4661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_4734_, lean_object* v_isMeta_4735_, lean_object* v_hint_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
uint8_t v_isMeta_boxed_4740_; lean_object* v_res_4741_; 
v_isMeta_boxed_4740_ = lean_unbox(v_isMeta_4735_);
v_res_4741_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_4734_, v_isMeta_boxed_4740_, v_hint_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_4742_, lean_object* v_declName_4743_, lean_object* v_as_4744_, size_t v_sz_4745_, size_t v_i_4746_, lean_object* v_b_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_){
_start:
{
uint8_t v___x_4751_; 
v___x_4751_ = lean_usize_dec_lt(v_i_4746_, v_sz_4745_);
if (v___x_4751_ == 0)
{
lean_object* v___x_4752_; 
lean_dec(v_declName_4743_);
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v_b_4747_);
return v___x_4752_;
}
else
{
lean_object* v___x_4753_; lean_object* v_modules_4754_; lean_object* v___x_4755_; lean_object* v_a_4756_; lean_object* v___x_4757_; lean_object* v_toImport_4758_; lean_object* v_module_4759_; lean_object* v___x_4760_; uint8_t v___x_4761_; lean_object* v___x_4762_; 
v___x_4753_ = l_Lean_Environment_header(v___x_4742_);
v_modules_4754_ = lean_ctor_get(v___x_4753_, 3);
lean_inc_ref(v_modules_4754_);
lean_dec_ref(v___x_4753_);
v___x_4755_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4756_ = lean_array_uget_borrowed(v_as_4744_, v_i_4746_);
v___x_4757_ = lean_array_get(v___x_4755_, v_modules_4754_, v_a_4756_);
lean_dec_ref(v_modules_4754_);
v_toImport_4758_ = lean_ctor_get(v___x_4757_, 0);
lean_inc_ref(v_toImport_4758_);
lean_dec(v___x_4757_);
v_module_4759_ = lean_ctor_get(v_toImport_4758_, 0);
lean_inc(v_module_4759_);
lean_dec_ref(v_toImport_4758_);
v___x_4760_ = lean_box(0);
v___x_4761_ = 0;
lean_inc(v_declName_4743_);
v___x_4762_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_4759_, v___x_4761_, v_declName_4743_, v___y_4748_, v___y_4749_);
if (lean_obj_tag(v___x_4762_) == 0)
{
size_t v___x_4763_; size_t v___x_4764_; 
lean_dec_ref_known(v___x_4762_, 1);
v___x_4763_ = ((size_t)1ULL);
v___x_4764_ = lean_usize_add(v_i_4746_, v___x_4763_);
v_i_4746_ = v___x_4764_;
v_b_4747_ = v___x_4760_;
goto _start;
}
else
{
lean_dec(v_declName_4743_);
return v___x_4762_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_4766_, lean_object* v_declName_4767_, lean_object* v_as_4768_, lean_object* v_sz_4769_, lean_object* v_i_4770_, lean_object* v_b_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
size_t v_sz_boxed_4775_; size_t v_i_boxed_4776_; lean_object* v_res_4777_; 
v_sz_boxed_4775_ = lean_unbox_usize(v_sz_4769_);
lean_dec(v_sz_4769_);
v_i_boxed_4776_ = lean_unbox_usize(v_i_4770_);
lean_dec(v_i_4770_);
v_res_4777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_4766_, v_declName_4767_, v_as_4768_, v_sz_boxed_4775_, v_i_boxed_4776_, v_b_4771_, v___y_4772_, v___y_4773_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec_ref(v_as_4768_);
lean_dec_ref(v___x_4766_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_4778_, uint8_t v_isMeta_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v_env_4788_; lean_object* v___y_4790_; lean_object* v___x_4803_; 
v___x_4783_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_4784_ = lean_st_ref_get(v___y_4781_);
v_env_4788_ = lean_ctor_get(v___x_4784_, 0);
lean_inc_ref(v_env_4788_);
lean_dec(v___x_4784_);
v___x_4803_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4788_, v_declName_4778_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_dec_ref(v_env_4788_);
lean_dec(v_declName_4778_);
goto v___jp_4785_;
}
else
{
lean_object* v_val_4804_; lean_object* v___x_4805_; lean_object* v_modules_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; 
v_val_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_val_4804_);
lean_dec_ref_known(v___x_4803_, 1);
v___x_4805_ = l_Lean_Environment_header(v_env_4788_);
v_modules_4806_ = lean_ctor_get(v___x_4805_, 3);
lean_inc_ref(v_modules_4806_);
lean_dec_ref(v___x_4805_);
v___x_4807_ = lean_array_get_size(v_modules_4806_);
v___x_4808_ = lean_nat_dec_lt(v_val_4804_, v___x_4807_);
if (v___x_4808_ == 0)
{
lean_dec_ref(v_modules_4806_);
lean_dec(v_val_4804_);
lean_dec_ref(v_env_4788_);
lean_dec(v_declName_4778_);
goto v___jp_4785_;
}
else
{
lean_object* v___x_4809_; lean_object* v___x_4810_; uint8_t v___y_4812_; 
v___x_4809_ = lean_array_fget(v_modules_4806_, v_val_4804_);
lean_dec(v_val_4804_);
lean_dec_ref(v_modules_4806_);
v___x_4810_ = lean_st_ref_get(v___y_4781_);
if (v_isMeta_4779_ == 0)
{
lean_dec(v___x_4810_);
v___y_4812_ = v_isMeta_4779_;
goto v___jp_4811_;
}
else
{
lean_object* v_env_4823_; uint8_t v___x_4824_; 
v_env_4823_ = lean_ctor_get(v___x_4810_, 0);
lean_inc_ref(v_env_4823_);
lean_dec(v___x_4810_);
lean_inc(v_declName_4778_);
v___x_4824_ = l_Lean_isMarkedMeta(v_env_4823_, v_declName_4778_);
if (v___x_4824_ == 0)
{
v___y_4812_ = v_isMeta_4779_;
goto v___jp_4811_;
}
else
{
uint8_t v___x_4825_; 
v___x_4825_ = 0;
v___y_4812_ = v___x_4825_;
goto v___jp_4811_;
}
}
v___jp_4811_:
{
lean_object* v_toImport_4813_; lean_object* v_module_4814_; lean_object* v___x_4815_; 
v_toImport_4813_ = lean_ctor_get(v___x_4809_, 0);
lean_inc_ref(v_toImport_4813_);
lean_dec(v___x_4809_);
v_module_4814_ = lean_ctor_get(v_toImport_4813_, 0);
lean_inc(v_module_4814_);
lean_dec_ref(v_toImport_4813_);
lean_inc(v_declName_4778_);
v___x_4815_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_4814_, v___y_4812_, v_declName_4778_, v___y_4780_, v___y_4781_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
lean_dec_ref_known(v___x_4815_, 1);
v___x_4816_ = l_Lean_indirectModUseExt;
v___x_4817_ = lean_box(1);
v___x_4818_ = lean_box(0);
lean_inc_ref(v_env_4788_);
v___x_4819_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4783_, v___x_4816_, v_env_4788_, v___x_4817_, v___x_4818_);
v___x_4820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4819_, v_declName_4778_);
lean_dec(v___x_4819_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v___x_4821_; 
v___x_4821_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_4790_ = v___x_4821_;
goto v___jp_4789_;
}
else
{
lean_object* v_val_4822_; 
v_val_4822_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_val_4822_);
lean_dec_ref_known(v___x_4820_, 1);
v___y_4790_ = v_val_4822_;
goto v___jp_4789_;
}
}
else
{
lean_dec_ref(v_env_4788_);
lean_dec(v_declName_4778_);
return v___x_4815_;
}
}
}
}
v___jp_4785_:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = lean_box(0);
v___x_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4786_);
return v___x_4787_;
}
v___jp_4789_:
{
lean_object* v___x_4791_; size_t v_sz_4792_; size_t v___x_4793_; lean_object* v___x_4794_; 
v___x_4791_ = lean_box(0);
v_sz_4792_ = lean_array_size(v___y_4790_);
v___x_4793_ = ((size_t)0ULL);
v___x_4794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_4788_, v_declName_4778_, v___y_4790_, v_sz_4792_, v___x_4793_, v___x_4791_, v___y_4780_, v___y_4781_);
lean_dec_ref(v___y_4790_);
lean_dec_ref(v_env_4788_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4801_; 
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4801_ == 0)
{
lean_object* v_unused_4802_; 
v_unused_4802_ = lean_ctor_get(v___x_4794_, 0);
lean_dec(v_unused_4802_);
v___x_4796_ = v___x_4794_;
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
else
{
lean_dec(v___x_4794_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 0, v___x_4791_);
v___x_4799_ = v___x_4796_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4791_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
else
{
return v___x_4794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_4826_, lean_object* v_isMeta_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
uint8_t v_isMeta_boxed_4831_; lean_object* v_res_4832_; 
v_isMeta_boxed_4831_ = lean_unbox(v_isMeta_4827_);
v_res_4832_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_4826_, v_isMeta_boxed_4831_, v___y_4828_, v___y_4829_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_){
_start:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4837_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4838_ = lean_st_ref_get(v___x_4837_);
v___x_4839_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4838_, v_attrName_4833_);
lean_dec(v___x_4838_);
if (lean_obj_tag(v___x_4839_) == 1)
{
lean_object* v_val_4840_; lean_object* v_ext_4841_; lean_object* v_name_4842_; uint8_t v___x_4843_; lean_object* v___x_4844_; 
v_val_4840_ = lean_ctor_get(v___x_4839_, 0);
v_ext_4841_ = lean_ctor_get(v_val_4840_, 1);
v_name_4842_ = lean_ctor_get(v_ext_4841_, 1);
v___x_4843_ = 1;
lean_inc(v_name_4842_);
v___x_4844_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_4842_, v___x_4843_, v_a_4834_, v_a_4835_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4851_; 
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4851_ == 0)
{
lean_object* v_unused_4852_; 
v_unused_4852_ = lean_ctor_get(v___x_4844_, 0);
lean_dec(v_unused_4852_);
v___x_4846_ = v___x_4844_;
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
else
{
lean_dec(v___x_4844_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4849_; 
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 0, v___x_4839_);
v___x_4849_ = v___x_4846_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4839_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_dec_ref_known(v___x_4839_, 1);
v_a_4853_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4844_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4844_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
else
{
lean_object* v___x_4861_; 
v___x_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4839_);
return v___x_4861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
lean_object* v_res_4866_; 
v_res_4866_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_4862_, v_a_4863_, v_a_4864_);
lean_dec(v_a_4864_);
lean_dec_ref(v_a_4863_);
lean_dec(v_attrName_4862_);
return v_res_4866_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_4867_; 
v___x_4867_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_4868_, lean_object* v_x_4869_){
_start:
{
if (lean_obj_tag(v_x_4869_) == 0)
{
return v_x_4868_;
}
else
{
lean_object* v_key_4870_; lean_object* v_value_4871_; lean_object* v_tail_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4898_; 
v_key_4870_ = lean_ctor_get(v_x_4869_, 0);
v_value_4871_ = lean_ctor_get(v_x_4869_, 1);
v_tail_4872_ = lean_ctor_get(v_x_4869_, 2);
v_isSharedCheck_4898_ = !lean_is_exclusive(v_x_4869_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4874_ = v_x_4869_;
v_isShared_4875_ = v_isSharedCheck_4898_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_tail_4872_);
lean_inc(v_value_4871_);
lean_inc(v_key_4870_);
lean_dec(v_x_4869_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4898_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4876_; uint64_t v___y_4878_; 
v___x_4876_ = lean_array_get_size(v_x_4868_);
if (lean_obj_tag(v_key_4870_) == 0)
{
uint64_t v___x_4896_; 
v___x_4896_ = 1723ULL;
v___y_4878_ = v___x_4896_;
goto v___jp_4877_;
}
else
{
uint64_t v_hash_4897_; 
v_hash_4897_ = lean_ctor_get_uint64(v_key_4870_, sizeof(void*)*2);
v___y_4878_ = v_hash_4897_;
goto v___jp_4877_;
}
v___jp_4877_:
{
uint64_t v___x_4879_; uint64_t v___x_4880_; uint64_t v_fold_4881_; uint64_t v___x_4882_; uint64_t v___x_4883_; uint64_t v___x_4884_; size_t v___x_4885_; size_t v___x_4886_; size_t v___x_4887_; size_t v___x_4888_; size_t v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4892_; 
v___x_4879_ = 32ULL;
v___x_4880_ = lean_uint64_shift_right(v___y_4878_, v___x_4879_);
v_fold_4881_ = lean_uint64_xor(v___y_4878_, v___x_4880_);
v___x_4882_ = 16ULL;
v___x_4883_ = lean_uint64_shift_right(v_fold_4881_, v___x_4882_);
v___x_4884_ = lean_uint64_xor(v_fold_4881_, v___x_4883_);
v___x_4885_ = lean_uint64_to_usize(v___x_4884_);
v___x_4886_ = lean_usize_of_nat(v___x_4876_);
v___x_4887_ = ((size_t)1ULL);
v___x_4888_ = lean_usize_sub(v___x_4886_, v___x_4887_);
v___x_4889_ = lean_usize_land(v___x_4885_, v___x_4888_);
v___x_4890_ = lean_array_uget_borrowed(v_x_4868_, v___x_4889_);
lean_inc(v___x_4890_);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 2, v___x_4890_);
v___x_4892_ = v___x_4874_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_key_4870_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v_value_4871_);
lean_ctor_set(v_reuseFailAlloc_4895_, 2, v___x_4890_);
v___x_4892_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
lean_object* v___x_4893_; 
v___x_4893_ = lean_array_uset(v_x_4868_, v___x_4889_, v___x_4892_);
v_x_4868_ = v___x_4893_;
v_x_4869_ = v_tail_4872_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4899_, lean_object* v_source_4900_, lean_object* v_target_4901_){
_start:
{
lean_object* v___x_4902_; uint8_t v___x_4903_; 
v___x_4902_ = lean_array_get_size(v_source_4900_);
v___x_4903_ = lean_nat_dec_lt(v_i_4899_, v___x_4902_);
if (v___x_4903_ == 0)
{
lean_dec_ref(v_source_4900_);
lean_dec(v_i_4899_);
return v_target_4901_;
}
else
{
lean_object* v_es_4904_; lean_object* v___x_4905_; lean_object* v_source_4906_; lean_object* v_target_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v_es_4904_ = lean_array_fget(v_source_4900_, v_i_4899_);
v___x_4905_ = lean_box(0);
v_source_4906_ = lean_array_fset(v_source_4900_, v_i_4899_, v___x_4905_);
v_target_4907_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_4901_, v_es_4904_);
v___x_4908_ = lean_unsigned_to_nat(1u);
v___x_4909_ = lean_nat_add(v_i_4899_, v___x_4908_);
lean_dec(v_i_4899_);
v_i_4899_ = v___x_4909_;
v_source_4900_ = v_source_4906_;
v_target_4901_ = v_target_4907_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_4911_){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v_nbuckets_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4912_ = lean_array_get_size(v_data_4911_);
v___x_4913_ = lean_unsigned_to_nat(2u);
v_nbuckets_4914_ = lean_nat_mul(v___x_4912_, v___x_4913_);
v___x_4915_ = lean_unsigned_to_nat(0u);
v___x_4916_ = lean_box(0);
v___x_4917_ = lean_mk_array(v_nbuckets_4914_, v___x_4916_);
v___x_4918_ = lean_array_propagate_mark(v_data_4911_, v___x_4917_);
v___x_4919_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_4915_, v_data_4911_, v___x_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_4920_, lean_object* v_x_4921_){
_start:
{
if (lean_obj_tag(v_x_4921_) == 0)
{
uint8_t v___x_4922_; 
v___x_4922_ = 0;
return v___x_4922_;
}
else
{
lean_object* v_key_4923_; lean_object* v_tail_4924_; uint8_t v___x_4925_; 
v_key_4923_ = lean_ctor_get(v_x_4921_, 0);
v_tail_4924_ = lean_ctor_get(v_x_4921_, 2);
v___x_4925_ = lean_name_eq(v_key_4923_, v_a_4920_);
if (v___x_4925_ == 0)
{
v_x_4921_ = v_tail_4924_;
goto _start;
}
else
{
return v___x_4925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_4927_, lean_object* v_x_4928_){
_start:
{
uint8_t v_res_4929_; lean_object* v_r_4930_; 
v_res_4929_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4927_, v_x_4928_);
lean_dec(v_x_4928_);
lean_dec(v_a_4927_);
v_r_4930_ = lean_box(v_res_4929_);
return v_r_4930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_4931_, lean_object* v_b_4932_, lean_object* v_x_4933_){
_start:
{
if (lean_obj_tag(v_x_4933_) == 0)
{
lean_dec(v_b_4932_);
lean_dec(v_a_4931_);
return v_x_4933_;
}
else
{
lean_object* v_key_4934_; lean_object* v_value_4935_; lean_object* v_tail_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4948_; 
v_key_4934_ = lean_ctor_get(v_x_4933_, 0);
v_value_4935_ = lean_ctor_get(v_x_4933_, 1);
v_tail_4936_ = lean_ctor_get(v_x_4933_, 2);
v_isSharedCheck_4948_ = !lean_is_exclusive(v_x_4933_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4938_ = v_x_4933_;
v_isShared_4939_ = v_isSharedCheck_4948_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_tail_4936_);
lean_inc(v_value_4935_);
lean_inc(v_key_4934_);
lean_dec(v_x_4933_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4948_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
uint8_t v___x_4940_; 
v___x_4940_ = lean_name_eq(v_key_4934_, v_a_4931_);
if (v___x_4940_ == 0)
{
lean_object* v___x_4941_; lean_object* v___x_4943_; 
v___x_4941_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4931_, v_b_4932_, v_tail_4936_);
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 2, v___x_4941_);
v___x_4943_ = v___x_4938_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_key_4934_);
lean_ctor_set(v_reuseFailAlloc_4944_, 1, v_value_4935_);
lean_ctor_set(v_reuseFailAlloc_4944_, 2, v___x_4941_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
else
{
lean_object* v___x_4946_; 
lean_dec(v_value_4935_);
lean_dec(v_key_4934_);
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 1, v_b_4932_);
lean_ctor_set(v___x_4938_, 0, v_a_4931_);
v___x_4946_ = v___x_4938_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4931_);
lean_ctor_set(v_reuseFailAlloc_4947_, 1, v_b_4932_);
lean_ctor_set(v_reuseFailAlloc_4947_, 2, v_tail_4936_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_4949_, lean_object* v_a_4950_, lean_object* v_b_4951_){
_start:
{
lean_object* v_size_4952_; lean_object* v_buckets_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4999_; 
v_size_4952_ = lean_ctor_get(v_m_4949_, 0);
v_buckets_4953_ = lean_ctor_get(v_m_4949_, 1);
v_isSharedCheck_4999_ = !lean_is_exclusive(v_m_4949_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4955_ = v_m_4949_;
v_isShared_4956_ = v_isSharedCheck_4999_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_buckets_4953_);
lean_inc(v_size_4952_);
lean_dec(v_m_4949_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4999_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4957_; uint64_t v___y_4959_; 
v___x_4957_ = lean_array_get_size(v_buckets_4953_);
if (lean_obj_tag(v_a_4950_) == 0)
{
uint64_t v___x_4997_; 
v___x_4997_ = 1723ULL;
v___y_4959_ = v___x_4997_;
goto v___jp_4958_;
}
else
{
uint64_t v_hash_4998_; 
v_hash_4998_ = lean_ctor_get_uint64(v_a_4950_, sizeof(void*)*2);
v___y_4959_ = v_hash_4998_;
goto v___jp_4958_;
}
v___jp_4958_:
{
uint64_t v___x_4960_; uint64_t v___x_4961_; uint64_t v_fold_4962_; uint64_t v___x_4963_; uint64_t v___x_4964_; uint64_t v___x_4965_; size_t v___x_4966_; size_t v___x_4967_; size_t v___x_4968_; size_t v___x_4969_; size_t v___x_4970_; lean_object* v_bkt_4971_; uint8_t v___x_4972_; 
v___x_4960_ = 32ULL;
v___x_4961_ = lean_uint64_shift_right(v___y_4959_, v___x_4960_);
v_fold_4962_ = lean_uint64_xor(v___y_4959_, v___x_4961_);
v___x_4963_ = 16ULL;
v___x_4964_ = lean_uint64_shift_right(v_fold_4962_, v___x_4963_);
v___x_4965_ = lean_uint64_xor(v_fold_4962_, v___x_4964_);
v___x_4966_ = lean_uint64_to_usize(v___x_4965_);
v___x_4967_ = lean_usize_of_nat(v___x_4957_);
v___x_4968_ = ((size_t)1ULL);
v___x_4969_ = lean_usize_sub(v___x_4967_, v___x_4968_);
v___x_4970_ = lean_usize_land(v___x_4966_, v___x_4969_);
v_bkt_4971_ = lean_array_uget_borrowed(v_buckets_4953_, v___x_4970_);
v___x_4972_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4950_, v_bkt_4971_);
if (v___x_4972_ == 0)
{
lean_object* v___x_4973_; lean_object* v_size_x27_4974_; lean_object* v___x_4975_; lean_object* v_buckets_x27_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; uint8_t v___x_4982_; 
v___x_4973_ = lean_unsigned_to_nat(1u);
v_size_x27_4974_ = lean_nat_add(v_size_4952_, v___x_4973_);
lean_dec(v_size_4952_);
lean_inc(v_bkt_4971_);
v___x_4975_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4975_, 0, v_a_4950_);
lean_ctor_set(v___x_4975_, 1, v_b_4951_);
lean_ctor_set(v___x_4975_, 2, v_bkt_4971_);
v_buckets_x27_4976_ = lean_array_uset(v_buckets_4953_, v___x_4970_, v___x_4975_);
v___x_4977_ = lean_unsigned_to_nat(4u);
v___x_4978_ = lean_nat_mul(v_size_x27_4974_, v___x_4977_);
v___x_4979_ = lean_unsigned_to_nat(3u);
v___x_4980_ = lean_nat_div(v___x_4978_, v___x_4979_);
lean_dec(v___x_4978_);
v___x_4981_ = lean_array_get_size(v_buckets_x27_4976_);
v___x_4982_ = lean_nat_dec_le(v___x_4980_, v___x_4981_);
lean_dec(v___x_4980_);
if (v___x_4982_ == 0)
{
lean_object* v_val_4983_; lean_object* v___x_4985_; 
v_val_4983_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_4976_);
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 1, v_val_4983_);
lean_ctor_set(v___x_4955_, 0, v_size_x27_4974_);
v___x_4985_ = v___x_4955_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_size_x27_4974_);
lean_ctor_set(v_reuseFailAlloc_4986_, 1, v_val_4983_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
return v___x_4985_;
}
}
else
{
lean_object* v___x_4988_; 
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 1, v_buckets_x27_4976_);
lean_ctor_set(v___x_4955_, 0, v_size_x27_4974_);
v___x_4988_ = v___x_4955_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_size_x27_4974_);
lean_ctor_set(v_reuseFailAlloc_4989_, 1, v_buckets_x27_4976_);
v___x_4988_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
return v___x_4988_;
}
}
}
else
{
lean_object* v___x_4990_; lean_object* v_buckets_x27_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4995_; 
lean_inc(v_bkt_4971_);
v___x_4990_ = lean_box(0);
v_buckets_x27_4991_ = lean_array_uset(v_buckets_4953_, v___x_4970_, v___x_4990_);
v___x_4992_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4950_, v_b_4951_, v_bkt_4971_);
v___x_4993_ = lean_array_uset(v_buckets_x27_4991_, v___x_4970_, v___x_4992_);
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 1, v___x_4993_);
v___x_4995_ = v___x_4955_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_size_4952_);
lean_ctor_set(v_reuseFailAlloc_4996_, 1, v___x_4993_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_5000_, lean_object* v_ref_5001_){
_start:
{
lean_object* v___x_5003_; 
lean_inc(v_ref_5001_);
v___x_5003_ = l_Lean_Meta_Grind_mkExtension(v_ref_5001_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; uint8_t v___x_5005_; uint8_t v___x_5006_; lean_object* v___x_5007_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc_n(v_a_5004_, 2);
lean_dec_ref_known(v___x_5003_, 1);
v___x_5005_ = 0;
v___x_5006_ = 1;
lean_inc(v_ref_5001_);
lean_inc(v_attrName_5000_);
v___x_5007_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_5000_, v___x_5005_, v___x_5006_, v_a_5004_, v_ref_5001_);
if (lean_obj_tag(v___x_5007_) == 0)
{
lean_object* v___x_5008_; 
lean_dec_ref_known(v___x_5007_, 1);
lean_inc(v_ref_5001_);
lean_inc(v_a_5004_);
lean_inc(v_attrName_5000_);
v___x_5008_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_5000_, v___x_5005_, v___x_5005_, v_a_5004_, v_ref_5001_);
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v___x_5009_; 
lean_dec_ref_known(v___x_5008_, 1);
lean_inc(v_ref_5001_);
lean_inc(v_a_5004_);
lean_inc(v_attrName_5000_);
v___x_5009_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_5000_, v___x_5006_, v___x_5006_, v_a_5004_, v_ref_5001_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v___x_5010_; 
lean_dec_ref_known(v___x_5009_, 1);
lean_inc(v_a_5004_);
lean_inc(v_attrName_5000_);
v___x_5010_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_5000_, v___x_5006_, v___x_5005_, v_a_5004_, v_ref_5001_);
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5021_; 
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_5010_);
if (v_isSharedCheck_5021_ == 0)
{
lean_object* v_unused_5022_; 
v_unused_5022_ = lean_ctor_get(v___x_5010_, 0);
lean_dec(v_unused_5022_);
v___x_5012_ = v___x_5010_;
v_isShared_5013_ = v_isSharedCheck_5021_;
goto v_resetjp_5011_;
}
else
{
lean_dec(v___x_5010_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5021_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5019_; 
v___x_5014_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_5015_ = lean_st_ref_take(v___x_5014_);
lean_inc(v_a_5004_);
v___x_5016_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_5015_, v_attrName_5000_, v_a_5004_);
v___x_5017_ = lean_st_ref_put(v___x_5014_, v___x_5016_);
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 0, v_a_5004_);
v___x_5019_ = v___x_5012_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5004_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
else
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5030_; 
lean_dec(v_a_5004_);
lean_dec(v_attrName_5000_);
v_a_5023_ = lean_ctor_get(v___x_5010_, 0);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_5010_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5025_ = v___x_5010_;
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v___x_5010_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v___x_5028_; 
if (v_isShared_5026_ == 0)
{
v___x_5028_ = v___x_5025_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_a_5023_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
}
}
}
}
else
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5038_; 
lean_dec(v_a_5004_);
lean_dec(v_ref_5001_);
lean_dec(v_attrName_5000_);
v_a_5031_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5033_ = v___x_5009_;
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v___x_5009_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5046_; 
lean_dec(v_a_5004_);
lean_dec(v_ref_5001_);
lean_dec(v_attrName_5000_);
v_a_5039_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5046_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_5041_ = v___x_5008_;
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5008_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5044_; 
if (v_isShared_5042_ == 0)
{
v___x_5044_ = v___x_5041_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_a_5039_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
return v___x_5044_;
}
}
}
}
else
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
lean_dec(v_a_5004_);
lean_dec(v_ref_5001_);
lean_dec(v_attrName_5000_);
v_a_5047_ = lean_ctor_get(v___x_5007_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5007_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_5007_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5007_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
else
{
lean_dec(v_ref_5001_);
lean_dec(v_attrName_5000_);
return v___x_5003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_5055_, lean_object* v_ref_5056_, lean_object* v_a_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l_Lean_Meta_Grind_registerAttr(v_attrName_5055_, v_ref_5056_);
return v_res_5058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_5059_, lean_object* v_m_5060_, lean_object* v_a_5061_, lean_object* v_b_5062_){
_start:
{
lean_object* v___x_5063_; 
v___x_5063_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_5060_, v_a_5061_, v_b_5062_);
return v___x_5063_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_5064_, lean_object* v_a_5065_, lean_object* v_x_5066_){
_start:
{
uint8_t v___x_5067_; 
v___x_5067_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_5065_, v_x_5066_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5068_, lean_object* v_a_5069_, lean_object* v_x_5070_){
_start:
{
uint8_t v_res_5071_; lean_object* v_r_5072_; 
v_res_5071_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_5068_, v_a_5069_, v_x_5070_);
lean_dec(v_x_5070_);
lean_dec(v_a_5069_);
v_r_5072_ = lean_box(v_res_5071_);
return v_r_5072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_5073_, lean_object* v_data_5074_){
_start:
{
lean_object* v___x_5075_; 
v___x_5075_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_5074_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_5076_, lean_object* v_a_5077_, lean_object* v_b_5078_, lean_object* v_x_5079_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_5077_, v_b_5078_, v_x_5079_);
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5081_, lean_object* v_i_5082_, lean_object* v_source_5083_, lean_object* v_target_5084_){
_start:
{
lean_object* v___x_5085_; 
v___x_5085_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_5082_, v_source_5083_, v_target_5084_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_5086_, lean_object* v_x_5087_, lean_object* v_x_5088_){
_start:
{
lean_object* v___x_5089_; 
v___x_5089_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_5087_, v_x_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_5097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_5098_ = l_Lean_Meta_Grind_registerAttr(v___x_5096_, v___x_5097_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_5099_){
_start:
{
lean_object* v_res_5100_; 
v_res_5100_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_5100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v___x_5111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_5112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_5113_ = l_Lean_Meta_Grind_registerAttr(v___x_5111_, v___x_5112_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_5114_){
_start:
{
lean_object* v_res_5115_; 
v_res_5115_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_5116_, lean_object* v_a_5117_){
_start:
{
lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v_env_5121_; lean_object* v___x_5122_; lean_object* v_ext_5123_; lean_object* v_toEnvExtension_5124_; lean_object* v_asyncMode_5125_; uint8_t v___x_5126_; lean_object* v___x_5127_; lean_object* v_casesTypes_5128_; uint8_t v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
v___x_5119_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_5120_ = lean_st_ref_get(v_a_5117_);
v_env_5121_ = lean_ctor_get(v___x_5120_, 0);
lean_inc_ref(v_env_5121_);
lean_dec(v___x_5120_);
v___x_5122_ = l_Lean_Meta_Grind_grindExt;
v_ext_5123_ = lean_ctor_get(v___x_5122_, 1);
v_toEnvExtension_5124_ = lean_ctor_get(v_ext_5123_, 0);
v_asyncMode_5125_ = lean_ctor_get(v_toEnvExtension_5124_, 2);
v___x_5126_ = 0;
v___x_5127_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5119_, v___x_5122_, v_env_5121_, v_asyncMode_5125_, v___x_5126_);
v_casesTypes_5128_ = lean_ctor_get(v___x_5127_, 0);
lean_inc_ref(v_casesTypes_5128_);
lean_dec(v___x_5127_);
v___x_5129_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_5128_, v_declName_5116_);
lean_dec_ref(v_casesTypes_5128_);
v___x_5130_ = lean_box(v___x_5129_);
v___x_5131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5131_, 0, v___x_5130_);
return v___x_5131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_){
_start:
{
lean_object* v_res_5135_; 
v_res_5135_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_5132_, v_a_5133_);
lean_dec(v_a_5133_);
lean_dec(v_declName_5132_);
return v_res_5135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_5136_, v_a_5138_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_5141_, v_a_5142_, v_a_5143_);
lean_dec(v_a_5143_);
lean_dec_ref(v_a_5142_);
lean_dec(v_declName_5141_);
return v_res_5145_;
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
