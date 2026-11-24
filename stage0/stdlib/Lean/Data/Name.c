// Lean compiler output
// Module: Lean.Data.Name
// Imports: public import Init.Data.Ord.Basic public import Init.Data.Iterators.Consumers.Loop import Init.Data.Iterators.Consumers.Collect import Init.Data.String.TakeDrop import Init.Data.Ord.String import Init.Data.Ord.UInt import Init.Data.String.Search import Init.Data.String.Length
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
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_string_compare(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint64_t lean_name_hash_exported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_hashEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix___boxed(lean_object*);
static const lean_string_object l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Name_getString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Data.Name"};
static const lean_object* l_Lean_Name_getString_x21___closed__0 = (const lean_object*)&l_Lean_Name_getString_x21___closed__0_value;
static const lean_string_object l_Lean_Name_getString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Name.getString!"};
static const lean_object* l_Lean_Name_getString_x21___closed__1 = (const lean_object*)&l_Lean_Name_getString_x21___closed__1_value;
static const lean_string_object l_Lean_Name_getString_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Name_getString_x21___closed__2 = (const lean_object*)&l_Lean_Name_getString_x21___closed__2_value;
static lean_once_cell_t l_Lean_Name_getString_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Name_getString_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_updatePrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_componentsRev(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_components(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_dropLastComponents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_dropLastComponents___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_instInhabitedRevComponentIterator_default;
LEAN_EXPORT lean_object* l_Lean_Name_instInhabitedRevComponentIterator;
LEAN_EXPORT lean_object* l_Lean_Name_revIter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_revIter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_step(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorOfPure___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorOfPure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_getPrefix_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_getPrefix_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_RevComponentIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_RevComponentIterator_finitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_RevComponentIterator_finitenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_RevComponentIterator_finitenessRelation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Name_instInhabitedComponentIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Name_instInhabitedComponentIterator___closed__0 = (const lean_object*)&l_Lean_Name_instInhabitedComponentIterator___closed__0_value;
static const lean_ctor_object l_Lean_Name_instInhabitedComponentIterator___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Name_instInhabitedComponentIterator___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Name_instInhabitedComponentIterator___closed__1 = (const lean_object*)&l_Lean_Name_instInhabitedComponentIterator___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Name_instInhabitedComponentIterator = (const lean_object*)&l_Lean_Name_instInhabitedComponentIterator___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Name_iter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_iter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Name_iter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_step(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorOfPure___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorOfPure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_ComponentIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_ComponentIterator_finitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_ComponentIterator_finitenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_ComponentIterator_finitenessRelation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_eqStr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_eqStr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isSuffixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_cmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_cmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_quickCmpAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_quickCmpAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isInternal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInternal___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isInternalOrNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInternalOrNum___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Name_isInternalDetail___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eq_"};
static const lean_object* l_Lean_Name_isInternalDetail___closed__0 = (const lean_object*)&l_Lean_Name_isInternalDetail___closed__0_value;
static const lean_string_object l_Lean_Name_isInternalDetail___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "match_"};
static const lean_object* l_Lean_Name_isInternalDetail___closed__1 = (const lean_object*)&l_Lean_Name_isInternalDetail___closed__1_value;
static const lean_string_object l_Lean_Name_isInternalDetail___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof_"};
static const lean_object* l_Lean_Name_isInternalDetail___closed__2 = (const lean_object*)&l_Lean_Name_isInternalDetail___closed__2_value;
static const lean_string_object l_Lean_Name_isInternalDetail___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "omega_"};
static const lean_object* l_Lean_Name_isInternalDetail___closed__3 = (const lean_object*)&l_Lean_Name_isInternalDetail___closed__3_value;
static const lean_string_object l_Lean_Name_isInternalDetail___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Name_isInternalDetail___closed__4 = (const lean_object*)&l_Lean_Name_isInternalDetail___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_Name_isInternalDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInternalDetail___boxed(lean_object*);
static const lean_string_object l_Lean_Name_isImplementationDetail___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "__"};
static const lean_object* l_Lean_Name_isImplementationDetail___closed__0 = (const lean_object*)&l_Lean_Name_isImplementationDetail___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isImplementationDetail___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isAtomic___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_hasSingleComponent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_hasSingleComponent___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isAnonymous___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isStr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isStr___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_isNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isNum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_anyS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_anyS___boxed(lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__3_value;
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Name_isMetaprogramming___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Name_isMetaprogramming___closed__0 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__0_value;
static const lean_ctor_object l_Lean_Name_isMetaprogramming___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Name_isMetaprogramming___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Name_isMetaprogramming___closed__1 = (const lean_object*)&l_Lean_Name_isMetaprogramming___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t lean_name_hash_exported(lean_object* v_a_1_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
uint64_t v___x_2_; 
v___x_2_ = 1723ULL;
return v___x_2_;
}
else
{
uint64_t v_hash_3_; 
v_hash_3_ = lean_ctor_get_uint64(v_a_1_, sizeof(void*)*2);
lean_dec(v_a_1_);
return v_hash_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_hashEx___boxed(lean_object* v_a_4_){
_start:
{
uint64_t v_res_5_; lean_object* v_r_6_; 
v_res_5_ = lean_name_hash_exported(v_a_4_);
v_r_6_ = lean_box_uint64(v_res_5_);
return v_r_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix(lean_object* v_x_7_){
_start:
{
if (lean_obj_tag(v_x_7_) == 0)
{
return v_x_7_;
}
else
{
lean_object* v_pre_8_; 
v_pre_8_ = lean_ctor_get(v_x_7_, 0);
lean_inc(v_pre_8_);
return v_pre_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getPrefix___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Name_getPrefix(v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Name_getString_x21_spec__0(lean_object* v_msg_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = ((lean_object*)(l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0));
v___x_14_ = lean_panic_fn_borrowed(v___x_13_, v_msg_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Name_getString_x21___closed__3(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_18_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__2));
v___x_19_ = lean_unsigned_to_nat(15u);
v___x_20_ = lean_unsigned_to_nat(33u);
v___x_21_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__1));
v___x_22_ = ((lean_object*)(l_Lean_Name_getString_x21___closed__0));
v___x_23_ = l_mkPanicMessageWithDecl(v___x_22_, v___x_21_, v___x_20_, v___x_19_, v___x_18_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21(lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_24_) == 1)
{
lean_object* v_str_25_; 
v_str_25_ = lean_ctor_get(v_x_24_, 1);
lean_inc_ref(v_str_25_);
return v_str_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&l_Lean_Name_getString_x21___closed__3, &l_Lean_Name_getString_x21___closed__3_once, _init_l_Lean_Name_getString_x21___closed__3);
v___x_27_ = l_panic___at___00Lean_Name_getString_x21_spec__0(v___x_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getString_x21___boxed(lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Name_getString_x21(v_x_28_);
lean_dec(v_x_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts(lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v___x_31_; 
v___x_31_ = lean_unsigned_to_nat(0u);
return v___x_31_;
}
else
{
lean_object* v_pre_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_pre_32_ = lean_ctor_get(v_x_30_, 0);
v___x_33_ = l_Lean_Name_getNumParts(v_pre_32_);
v___x_34_ = lean_unsigned_to_nat(1u);
v___x_35_ = lean_nat_add(v___x_33_, v___x_34_);
lean_dec(v___x_33_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getNumParts___boxed(lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Name_getNumParts(v_x_36_);
lean_dec(v_x_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_updatePrefix(lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
switch(lean_obj_tag(v_x_38_))
{
case 0:
{
lean_dec(v_x_39_);
return v_x_38_;
}
case 1:
{
lean_object* v_str_40_; lean_object* v___x_41_; 
v_str_40_ = lean_ctor_get(v_x_38_, 1);
lean_inc_ref(v_str_40_);
lean_dec_ref_known(v_x_38_, 2);
v___x_41_ = l_Lean_Name_str___override(v_x_39_, v_str_40_);
return v___x_41_;
}
default: 
{
lean_object* v_i_42_; lean_object* v___x_43_; 
v_i_42_ = lean_ctor_get(v_x_38_, 1);
lean_inc(v_i_42_);
lean_dec_ref_known(v_x_38_, 2);
v___x_43_ = l_Lean_Name_num___override(v_x_39_, v_i_42_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_componentsRev(lean_object* v_x_44_){
_start:
{
switch(lean_obj_tag(v_x_44_))
{
case 0:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
case 1:
{
lean_object* v_pre_46_; lean_object* v_str_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_pre_46_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_pre_46_);
v_str_47_ = lean_ctor_get(v_x_44_, 1);
lean_inc_ref(v_str_47_);
lean_dec_ref_known(v_x_44_, 2);
v___x_48_ = lean_box(0);
v___x_49_ = l_Lean_Name_str___override(v___x_48_, v_str_47_);
v___x_50_ = l_Lean_Name_componentsRev(v_pre_46_);
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
return v___x_51_;
}
default: 
{
lean_object* v_pre_52_; lean_object* v_i_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_pre_52_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_pre_52_);
v_i_53_ = lean_ctor_get(v_x_44_, 1);
lean_inc(v_i_53_);
lean_dec_ref_known(v_x_44_, 2);
v___x_54_ = lean_box(0);
v___x_55_ = l_Lean_Name_num___override(v___x_54_, v_i_53_);
v___x_56_ = l_Lean_Name_componentsRev(v_pre_52_);
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_components(lean_object* v_n_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = l_Lean_Name_componentsRev(v_n_58_);
v___x_60_ = l_List_reverse___redArg(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_dropLastComponents(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
lean_object* v_zero_63_; uint8_t v_isZero_64_; 
v_zero_63_ = lean_unsigned_to_nat(0u);
v_isZero_64_ = lean_nat_dec_eq(v_x_62_, v_zero_63_);
if (v_isZero_64_ == 1)
{
lean_dec(v_x_62_);
lean_inc(v_x_61_);
return v_x_61_;
}
else
{
lean_object* v_one_65_; lean_object* v_n_66_; 
v_one_65_ = lean_unsigned_to_nat(1u);
v_n_66_ = lean_nat_sub(v_x_62_, v_one_65_);
lean_dec(v_x_62_);
if (lean_obj_tag(v_x_61_) == 0)
{
lean_dec(v_n_66_);
return v_x_61_;
}
else
{
lean_object* v_pre_67_; 
v_pre_67_ = lean_ctor_get(v_x_61_, 0);
v_x_61_ = v_pre_67_;
v_x_62_ = v_n_66_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_dropLastComponents___boxed(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Name_dropLastComponents(v_x_69_, v_x_70_);
lean_dec(v_x_69_);
return v_res_71_;
}
}
static lean_object* _init_l_Lean_Name_instInhabitedRevComponentIterator_default(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_box(0);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Name_instInhabitedRevComponentIterator(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_revIter(lean_object* v_n_74_){
_start:
{
lean_inc(v_n_74_);
return v_n_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_revIter___boxed(lean_object* v_n_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Name_revIter(v_n_75_);
lean_dec(v_n_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_step___redArg(lean_object* v_x_77_){
_start:
{
switch(lean_obj_tag(v_x_77_))
{
case 0:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(2);
return v___x_78_;
}
case 1:
{
lean_object* v_pre_79_; lean_object* v_str_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_pre_79_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_pre_79_);
v_str_80_ = lean_ctor_get(v_x_77_, 1);
lean_inc_ref(v_str_80_);
lean_dec_ref_known(v_x_77_, 2);
v___x_81_ = lean_box(0);
v___x_82_ = l_Lean_Name_str___override(v___x_81_, v_str_80_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v_pre_79_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
return v___x_83_;
}
default: 
{
lean_object* v_pre_84_; lean_object* v_i_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_pre_84_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_pre_84_);
v_i_85_ = lean_ctor_get(v_x_77_, 1);
lean_inc(v_i_85_);
lean_dec_ref_known(v_x_77_, 2);
v___x_86_ = lean_box(0);
v___x_87_ = l_Lean_Name_num___override(v___x_86_, v_i_85_);
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v_pre_84_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_step(lean_object* v_m_89_, lean_object* v_x_90_){
_start:
{
switch(lean_obj_tag(v_x_90_))
{
case 0:
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(2);
return v___x_91_;
}
case 1:
{
lean_object* v_pre_92_; lean_object* v_str_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_pre_92_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_pre_92_);
v_str_93_ = lean_ctor_get(v_x_90_, 1);
lean_inc_ref(v_str_93_);
lean_dec_ref_known(v_x_90_, 2);
v___x_94_ = lean_box(0);
v___x_95_ = l_Lean_Name_str___override(v___x_94_, v_str_93_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_pre_92_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
return v___x_96_;
}
default: 
{
lean_object* v_pre_97_; lean_object* v_i_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_pre_97_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_pre_97_);
v_i_98_ = lean_ctor_get(v_x_90_, 1);
lean_inc(v_i_98_);
lean_dec_ref_known(v_x_90_, 2);
v___x_99_ = lean_box(0);
v___x_100_ = l_Lean_Name_num___override(v___x_99_, v_i_98_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v_pre_97_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorOfPure___redArg___lam__0(lean_object* v_inst_102_, lean_object* v_it_103_){
_start:
{
switch(lean_obj_tag(v_it_103_))
{
case 0:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_box(2);
v___x_105_ = lean_apply_2(v_inst_102_, lean_box(0), v___x_104_);
return v___x_105_;
}
case 1:
{
lean_object* v_pre_106_; lean_object* v_str_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_pre_106_ = lean_ctor_get(v_it_103_, 0);
lean_inc(v_pre_106_);
v_str_107_ = lean_ctor_get(v_it_103_, 1);
lean_inc_ref(v_str_107_);
lean_dec_ref_known(v_it_103_, 2);
v___x_108_ = lean_box(0);
v___x_109_ = l_Lean_Name_str___override(v___x_108_, v_str_107_);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v_pre_106_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = lean_apply_2(v_inst_102_, lean_box(0), v___x_110_);
return v___x_111_;
}
default: 
{
lean_object* v_pre_112_; lean_object* v_i_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_pre_112_ = lean_ctor_get(v_it_103_, 0);
lean_inc(v_pre_112_);
v_i_113_ = lean_ctor_get(v_it_103_, 1);
lean_inc(v_i_113_);
lean_dec_ref_known(v_it_103_, 2);
v___x_114_ = lean_box(0);
v___x_115_ = l_Lean_Name_num___override(v___x_114_, v_i_113_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v_pre_112_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_apply_2(v_inst_102_, lean_box(0), v___x_116_);
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorOfPure___redArg(lean_object* v_inst_118_){
_start:
{
lean_object* v___f_119_; 
v___f_119_ = lean_alloc_closure((void*)(l_Lean_Name_RevComponentIterator_instIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_119_, 0, v_inst_118_);
return v___f_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorOfPure(lean_object* v_m_120_, lean_object* v_inst_121_){
_start:
{
lean_object* v___f_122_; 
v___f_122_ = lean_alloc_closure((void*)(l_Lean_Name_RevComponentIterator_instIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_122_, 0, v_inst_121_);
return v___f_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_getPrefix_match__1_splitter___redArg(lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_, lean_object* v_h__3_126_){
_start:
{
switch(lean_obj_tag(v_x_123_))
{
case 0:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_h__3_126_);
lean_dec(v_h__2_125_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_apply_1(v_h__1_124_, v___x_127_);
return v___x_128_;
}
case 1:
{
lean_object* v_pre_129_; lean_object* v_str_130_; lean_object* v___x_131_; 
lean_dec(v_h__3_126_);
lean_dec(v_h__1_124_);
v_pre_129_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_pre_129_);
v_str_130_ = lean_ctor_get(v_x_123_, 1);
lean_inc_ref(v_str_130_);
lean_dec_ref_known(v_x_123_, 2);
v___x_131_ = lean_apply_2(v_h__2_125_, v_pre_129_, v_str_130_);
return v___x_131_;
}
default: 
{
lean_object* v_pre_132_; lean_object* v_i_133_; lean_object* v___x_134_; 
lean_dec(v_h__2_125_);
lean_dec(v_h__1_124_);
v_pre_132_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_pre_132_);
v_i_133_ = lean_ctor_get(v_x_123_, 1);
lean_inc(v_i_133_);
lean_dec_ref_known(v_x_123_, 2);
v___x_134_ = lean_apply_2(v_h__3_126_, v_pre_132_, v_i_133_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_getPrefix_match__1_splitter(lean_object* v_motive_135_, lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_, lean_object* v_h__3_139_){
_start:
{
switch(lean_obj_tag(v_x_136_))
{
case 0:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v_h__3_139_);
lean_dec(v_h__2_138_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_apply_1(v_h__1_137_, v___x_140_);
return v___x_141_;
}
case 1:
{
lean_object* v_pre_142_; lean_object* v_str_143_; lean_object* v___x_144_; 
lean_dec(v_h__3_139_);
lean_dec(v_h__1_137_);
v_pre_142_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_pre_142_);
v_str_143_ = lean_ctor_get(v_x_136_, 1);
lean_inc_ref(v_str_143_);
lean_dec_ref_known(v_x_136_, 2);
v___x_144_ = lean_apply_2(v_h__2_138_, v_pre_142_, v_str_143_);
return v___x_144_;
}
default: 
{
lean_object* v_pre_145_; lean_object* v_i_146_; lean_object* v___x_147_; 
lean_dec(v_h__2_138_);
lean_dec(v_h__1_137_);
v_pre_145_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_pre_145_);
v_i_146_ = lean_ctor_get(v_x_136_, 1);
lean_inc(v_i_146_);
lean_dec_ref_known(v_x_136_, 2);
v___x_147_ = lean_apply_2(v_h__3_139_, v_pre_145_, v_i_146_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_RevComponentIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_box(0);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_RevComponentIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Data_Name_0__Lean_Name_RevComponentIterator_finitenessRelation___redArg();
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_RevComponentIterator_finitenessRelation(lean_object* v_m_152_, lean_object* v_inst_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(0);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_RevComponentIterator_finitenessRelation___boxed(lean_object* v_m_155_, lean_object* v_inst_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Data_Name_0__Lean_Name_RevComponentIterator_finitenessRelation(v_m_155_, v_inst_156_);
lean_dec(v_inst_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object* v_toPure_158_, lean_object* v_recur_159_, lean_object* v_it_160_, lean_object* v_____do__lift_161_){
_start:
{
if (lean_obj_tag(v_____do__lift_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_163_; 
lean_dec(v_it_160_);
lean_dec(v_recur_159_);
v_a_162_ = lean_ctor_get(v_____do__lift_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref_known(v_____do__lift_161_, 1);
v___x_163_ = lean_apply_2(v_toPure_158_, lean_box(0), v_a_162_);
return v___x_163_;
}
else
{
lean_object* v_a_164_; lean_object* v___x_165_; 
lean_dec(v_toPure_158_);
v_a_164_ = lean_ctor_get(v_____do__lift_161_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v_____do__lift_161_, 1);
v___x_165_ = lean_apply_4(v_recur_159_, v_it_160_, v_a_164_, lean_box(0), lean_box(0));
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object* v_toPure_166_, lean_object* v_recur_167_, lean_object* v___y_168_, lean_object* v_acc_169_, lean_object* v_toBind_170_, lean_object* v_s_171_){
_start:
{
switch(lean_obj_tag(v_s_171_))
{
case 0:
{
lean_object* v_it_172_; lean_object* v_out_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_it_172_ = lean_ctor_get(v_s_171_, 0);
lean_inc(v_it_172_);
v_out_173_ = lean_ctor_get(v_s_171_, 1);
lean_inc(v_out_173_);
lean_dec_ref_known(v_s_171_, 2);
v___f_174_ = lean_alloc_closure((void*)(l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_174_, 0, v_toPure_166_);
lean_closure_set(v___f_174_, 1, v_recur_167_);
lean_closure_set(v___f_174_, 2, v_it_172_);
v___x_175_ = lean_apply_3(v___y_168_, v_out_173_, lean_box(0), v_acc_169_);
v___x_176_ = lean_apply_4(v_toBind_170_, lean_box(0), lean_box(0), v___x_175_, v___f_174_);
return v___x_176_;
}
case 1:
{
lean_object* v_it_177_; lean_object* v___x_178_; 
lean_dec(v_toBind_170_);
lean_dec(v___y_168_);
lean_dec(v_toPure_166_);
v_it_177_ = lean_ctor_get(v_s_171_, 0);
lean_inc(v_it_177_);
lean_dec_ref_known(v_s_171_, 1);
v___x_178_ = lean_apply_4(v_recur_167_, v_it_177_, v_acc_169_, lean_box(0), lean_box(0));
return v___x_178_;
}
default: 
{
lean_object* v___x_179_; 
lean_dec(v_toBind_170_);
lean_dec(v___y_168_);
lean_dec(v_recur_167_);
v___x_179_ = lean_apply_2(v_toPure_166_, lean_box(0), v_acc_169_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object* v_toPure_180_, lean_object* v___y_181_, lean_object* v_toBind_182_, lean_object* v_toPure_183_, lean_object* v_lift_184_, lean_object* v_it_185_, lean_object* v_acc_186_, lean_object* v_hP_187_, lean_object* v_recur_188_){
_start:
{
lean_object* v___f_189_; lean_object* v___y_191_; 
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_189_, 0, v_toPure_180_);
lean_closure_set(v___f_189_, 1, v_recur_188_);
lean_closure_set(v___f_189_, 2, v___y_181_);
lean_closure_set(v___f_189_, 3, v_acc_186_);
lean_closure_set(v___f_189_, 4, v_toBind_182_);
switch(lean_obj_tag(v_it_185_))
{
case 0:
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(2);
v___y_191_ = v___x_194_;
goto v___jp_190_;
}
case 1:
{
lean_object* v_pre_195_; lean_object* v_str_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_pre_195_ = lean_ctor_get(v_it_185_, 0);
lean_inc(v_pre_195_);
v_str_196_ = lean_ctor_get(v_it_185_, 1);
lean_inc_ref(v_str_196_);
lean_dec_ref_known(v_it_185_, 2);
v___x_197_ = lean_box(0);
v___x_198_ = l_Lean_Name_str___override(v___x_197_, v_str_196_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v_pre_195_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___y_191_ = v___x_199_;
goto v___jp_190_;
}
default: 
{
lean_object* v_pre_200_; lean_object* v_i_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_pre_200_ = lean_ctor_get(v_it_185_, 0);
lean_inc(v_pre_200_);
v_i_201_ = lean_ctor_get(v_it_185_, 1);
lean_inc(v_i_201_);
lean_dec_ref_known(v_it_185_, 2);
v___x_202_ = lean_box(0);
v___x_203_ = l_Lean_Name_num___override(v___x_202_, v_i_201_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_pre_200_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___y_191_ = v___x_204_;
goto v___jp_190_;
}
}
v___jp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_apply_2(v_toPure_183_, lean_box(0), v___y_191_);
v___x_193_ = lean_apply_4(v_lift_184_, lean_box(0), lean_box(0), v___f_189_, v___x_192_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object* v_inst_205_, lean_object* v_toPure_206_, lean_object* v_lift_207_, lean_object* v_00_u03b3_208_, lean_object* v_Pl_209_, lean_object* v_it_210_, lean_object* v_init_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_toApplicative_213_; lean_object* v_toBind_214_; lean_object* v_toPure_215_; lean_object* v___f_216_; lean_object* v___x_217_; 
v_toApplicative_213_ = lean_ctor_get(v_inst_205_, 0);
lean_inc_ref(v_toApplicative_213_);
v_toBind_214_ = lean_ctor_get(v_inst_205_, 1);
lean_inc(v_toBind_214_);
lean_dec_ref(v_inst_205_);
v_toPure_215_ = lean_ctor_get(v_toApplicative_213_, 1);
lean_inc(v_toPure_215_);
lean_dec_ref(v_toApplicative_213_);
v___f_216_ = lean_alloc_closure((void*)(l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__2), 9, 5);
lean_closure_set(v___f_216_, 0, v_toPure_215_);
lean_closure_set(v___f_216_, 1, v___y_212_);
lean_closure_set(v___f_216_, 2, v_toBind_214_);
lean_closure_set(v___f_216_, 3, v_toPure_206_);
lean_closure_set(v___f_216_, 4, v_lift_207_);
v___x_217_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_216_, v_it_210_, v_init_211_, lean_box(0));
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg(lean_object* v_inst_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v_toApplicative_220_; lean_object* v_toPure_221_; lean_object* v___f_222_; 
v_toApplicative_220_ = lean_ctor_get(v_inst_218_, 0);
lean_inc_ref(v_toApplicative_220_);
lean_dec_ref(v_inst_218_);
v_toPure_221_ = lean_ctor_get(v_toApplicative_220_, 1);
lean_inc(v_toPure_221_);
lean_dec_ref(v_toApplicative_220_);
v___f_222_ = lean_alloc_closure((void*)(l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg___lam__3), 8, 2);
lean_closure_set(v___f_222_, 0, v_inst_219_);
lean_closure_set(v___f_222_, 1, v_toPure_221_);
return v___f_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad(lean_object* v_m_223_, lean_object* v_n_224_, lean_object* v_inst_225_, lean_object* v_inst_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Name_RevComponentIterator_instIteratorLoopOfMonad___redArg(v_inst_225_, v_inst_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Name_iter_spec__0___redArg(lean_object* v_a_234_, lean_object* v_b_235_){
_start:
{
lean_object* v_it_237_; lean_object* v_out_238_; 
switch(lean_obj_tag(v_a_234_))
{
case 0:
{
return v_b_235_;
}
case 1:
{
lean_object* v_pre_241_; lean_object* v_str_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_pre_241_ = lean_ctor_get(v_a_234_, 0);
lean_inc(v_pre_241_);
v_str_242_ = lean_ctor_get(v_a_234_, 1);
lean_inc_ref(v_str_242_);
lean_dec_ref_known(v_a_234_, 2);
v___x_243_ = lean_box(0);
v___x_244_ = l_Lean_Name_str___override(v___x_243_, v_str_242_);
v_it_237_ = v_pre_241_;
v_out_238_ = v___x_244_;
goto v___jp_236_;
}
default: 
{
lean_object* v_pre_245_; lean_object* v_i_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_pre_245_ = lean_ctor_get(v_a_234_, 0);
lean_inc(v_pre_245_);
v_i_246_ = lean_ctor_get(v_a_234_, 1);
lean_inc(v_i_246_);
lean_dec_ref_known(v_a_234_, 2);
v___x_247_ = lean_box(0);
v___x_248_ = l_Lean_Name_num___override(v___x_247_, v_i_246_);
v_it_237_ = v_pre_245_;
v_out_238_ = v___x_248_;
goto v___jp_236_;
}
}
v___jp_236_:
{
lean_object* v___x_239_; 
v___x_239_ = lean_array_push(v_b_235_, v_out_238_);
v_a_234_ = v_it_237_;
v_b_235_ = v___x_239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_iter(lean_object* v_n_249_){
_start:
{
lean_object* v___x_250_; lean_object* v_revComponents_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_250_ = ((lean_object*)(l_Lean_Name_instInhabitedComponentIterator___closed__0));
v_revComponents_251_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Name_iter_spec__0___redArg(v_n_249_, v___x_250_);
v___x_252_ = lean_array_get_size(v_revComponents_251_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_revComponents_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Name_iter_spec__0(lean_object* v_inst_254_, lean_object* v_R_255_, lean_object* v_a_256_, lean_object* v_b_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Name_iter_spec__0___redArg(v_a_256_, v_b_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_step___redArg(lean_object* v_x_259_){
_start:
{
lean_object* v_revComponents_260_; lean_object* v_pos_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_275_; 
v_revComponents_260_ = lean_ctor_get(v_x_259_, 0);
v_pos_261_ = lean_ctor_get(v_x_259_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_275_ == 0)
{
v___x_263_ = v_x_259_;
v_isShared_264_ = v_isSharedCheck_275_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_pos_261_);
lean_inc(v_revComponents_260_);
lean_dec(v_x_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_275_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_zero_265_; uint8_t v_isZero_266_; 
v_zero_265_ = lean_unsigned_to_nat(0u);
v_isZero_266_ = lean_nat_dec_eq(v_pos_261_, v_zero_265_);
if (v_isZero_266_ == 1)
{
lean_object* v___x_267_; 
lean_del_object(v___x_263_);
lean_dec(v_pos_261_);
lean_dec_ref(v_revComponents_260_);
v___x_267_ = lean_box(2);
return v___x_267_;
}
else
{
lean_object* v_one_268_; lean_object* v_n_269_; lean_object* v___x_271_; 
v_one_268_ = lean_unsigned_to_nat(1u);
v_n_269_ = lean_nat_sub(v_pos_261_, v_one_268_);
lean_dec(v_pos_261_);
lean_inc(v_n_269_);
lean_inc_ref(v_revComponents_260_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v_n_269_);
v___x_271_ = v___x_263_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_revComponents_260_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_n_269_);
v___x_271_ = v_reuseFailAlloc_274_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_array_fget(v_revComponents_260_, v_n_269_);
lean_dec(v_n_269_);
lean_dec_ref(v_revComponents_260_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_step(lean_object* v_m_276_, lean_object* v_x_277_){
_start:
{
lean_object* v_revComponents_278_; lean_object* v_pos_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_293_; 
v_revComponents_278_ = lean_ctor_get(v_x_277_, 0);
v_pos_279_ = lean_ctor_get(v_x_277_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_293_ == 0)
{
v___x_281_ = v_x_277_;
v_isShared_282_ = v_isSharedCheck_293_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_pos_279_);
lean_inc(v_revComponents_278_);
lean_dec(v_x_277_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_293_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_zero_283_; uint8_t v_isZero_284_; 
v_zero_283_ = lean_unsigned_to_nat(0u);
v_isZero_284_ = lean_nat_dec_eq(v_pos_279_, v_zero_283_);
if (v_isZero_284_ == 1)
{
lean_object* v___x_285_; 
lean_del_object(v___x_281_);
lean_dec(v_pos_279_);
lean_dec_ref(v_revComponents_278_);
v___x_285_ = lean_box(2);
return v___x_285_;
}
else
{
lean_object* v_one_286_; lean_object* v_n_287_; lean_object* v___x_289_; 
v_one_286_ = lean_unsigned_to_nat(1u);
v_n_287_ = lean_nat_sub(v_pos_279_, v_one_286_);
lean_dec(v_pos_279_);
lean_inc(v_n_287_);
lean_inc_ref(v_revComponents_278_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v_n_287_);
v___x_289_ = v___x_281_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_revComponents_278_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_n_287_);
v___x_289_ = v_reuseFailAlloc_292_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_array_fget(v_revComponents_278_, v_n_287_);
lean_dec(v_n_287_);
lean_dec_ref(v_revComponents_278_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorOfPure___redArg___lam__0(lean_object* v_inst_294_, lean_object* v_it_295_){
_start:
{
lean_object* v_revComponents_296_; lean_object* v_pos_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_313_; 
v_revComponents_296_ = lean_ctor_get(v_it_295_, 0);
v_pos_297_ = lean_ctor_get(v_it_295_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v_it_295_);
if (v_isSharedCheck_313_ == 0)
{
v___x_299_ = v_it_295_;
v_isShared_300_ = v_isSharedCheck_313_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_pos_297_);
lean_inc(v_revComponents_296_);
lean_dec(v_it_295_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_313_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_zero_301_; uint8_t v_isZero_302_; 
v_zero_301_ = lean_unsigned_to_nat(0u);
v_isZero_302_ = lean_nat_dec_eq(v_pos_297_, v_zero_301_);
if (v_isZero_302_ == 1)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_del_object(v___x_299_);
lean_dec(v_pos_297_);
lean_dec_ref(v_revComponents_296_);
v___x_303_ = lean_box(2);
v___x_304_ = lean_apply_2(v_inst_294_, lean_box(0), v___x_303_);
return v___x_304_;
}
else
{
lean_object* v_one_305_; lean_object* v_n_306_; lean_object* v___x_308_; 
v_one_305_ = lean_unsigned_to_nat(1u);
v_n_306_ = lean_nat_sub(v_pos_297_, v_one_305_);
lean_dec(v_pos_297_);
lean_inc(v_n_306_);
lean_inc_ref(v_revComponents_296_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_n_306_);
v___x_308_ = v___x_299_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_revComponents_296_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_n_306_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_array_fget(v_revComponents_296_, v_n_306_);
lean_dec(v_n_306_);
lean_dec_ref(v_revComponents_296_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_apply_2(v_inst_294_, lean_box(0), v___x_310_);
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorOfPure___redArg(lean_object* v_inst_314_){
_start:
{
lean_object* v___f_315_; 
v___f_315_ = lean_alloc_closure((void*)(l_Lean_Name_ComponentIterator_instIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_315_, 0, v_inst_314_);
return v___f_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorOfPure(lean_object* v_m_316_, lean_object* v_inst_317_){
_start:
{
lean_object* v___f_318_; 
v___f_318_ = lean_alloc_closure((void*)(l_Lean_Name_ComponentIterator_instIteratorOfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_318_, 0, v_inst_317_);
return v___f_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_ComponentIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_box(0);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_ComponentIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Data_Name_0__Lean_Name_ComponentIterator_finitenessRelation___redArg();
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_ComponentIterator_finitenessRelation(lean_object* v_m_323_, lean_object* v_inst_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(0);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_ComponentIterator_finitenessRelation___boxed(lean_object* v_m_326_, lean_object* v_inst_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Data_Name_0__Lean_Name_ComponentIterator_finitenessRelation(v_m_326_, v_inst_327_);
lean_dec(v_inst_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object* v_toPure_329_, lean_object* v_recur_330_, lean_object* v_it_331_, lean_object* v_____do__lift_332_){
_start:
{
if (lean_obj_tag(v_____do__lift_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_334_; 
lean_dec_ref(v_it_331_);
lean_dec(v_recur_330_);
v_a_333_ = lean_ctor_get(v_____do__lift_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref_known(v_____do__lift_332_, 1);
v___x_334_ = lean_apply_2(v_toPure_329_, lean_box(0), v_a_333_);
return v___x_334_;
}
else
{
lean_object* v_a_335_; lean_object* v___x_336_; 
lean_dec(v_toPure_329_);
v_a_335_ = lean_ctor_get(v_____do__lift_332_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v_____do__lift_332_, 1);
v___x_336_ = lean_apply_4(v_recur_330_, v_it_331_, v_a_335_, lean_box(0), lean_box(0));
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object* v_toPure_337_, lean_object* v_recur_338_, lean_object* v___y_339_, lean_object* v_acc_340_, lean_object* v_toBind_341_, lean_object* v_s_342_){
_start:
{
switch(lean_obj_tag(v_s_342_))
{
case 0:
{
lean_object* v_it_343_; lean_object* v_out_344_; lean_object* v___f_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_it_343_ = lean_ctor_get(v_s_342_, 0);
lean_inc(v_it_343_);
v_out_344_ = lean_ctor_get(v_s_342_, 1);
lean_inc(v_out_344_);
lean_dec_ref_known(v_s_342_, 2);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_345_, 0, v_toPure_337_);
lean_closure_set(v___f_345_, 1, v_recur_338_);
lean_closure_set(v___f_345_, 2, v_it_343_);
v___x_346_ = lean_apply_3(v___y_339_, v_out_344_, lean_box(0), v_acc_340_);
v___x_347_ = lean_apply_4(v_toBind_341_, lean_box(0), lean_box(0), v___x_346_, v___f_345_);
return v___x_347_;
}
case 1:
{
lean_object* v_it_348_; lean_object* v___x_349_; 
lean_dec(v_toBind_341_);
lean_dec(v___y_339_);
lean_dec(v_toPure_337_);
v_it_348_ = lean_ctor_get(v_s_342_, 0);
lean_inc(v_it_348_);
lean_dec_ref_known(v_s_342_, 1);
v___x_349_ = lean_apply_4(v_recur_338_, v_it_348_, v_acc_340_, lean_box(0), lean_box(0));
return v___x_349_;
}
default: 
{
lean_object* v___x_350_; 
lean_dec(v_toBind_341_);
lean_dec(v___y_339_);
lean_dec(v_recur_338_);
v___x_350_ = lean_apply_2(v_toPure_337_, lean_box(0), v_acc_340_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object* v_toPure_351_, lean_object* v___y_352_, lean_object* v_toBind_353_, lean_object* v_toPure_354_, lean_object* v_lift_355_, lean_object* v_it_356_, lean_object* v_acc_357_, lean_object* v_hP_358_, lean_object* v_recur_359_){
_start:
{
lean_object* v_revComponents_360_; lean_object* v_pos_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_380_; 
v_revComponents_360_ = lean_ctor_get(v_it_356_, 0);
v_pos_361_ = lean_ctor_get(v_it_356_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_it_356_);
if (v_isSharedCheck_380_ == 0)
{
v___x_363_ = v_it_356_;
v_isShared_364_ = v_isSharedCheck_380_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_pos_361_);
lean_inc(v_revComponents_360_);
lean_dec(v_it_356_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_380_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___f_365_; lean_object* v___y_367_; lean_object* v_zero_370_; uint8_t v_isZero_371_; 
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_365_, 0, v_toPure_351_);
lean_closure_set(v___f_365_, 1, v_recur_359_);
lean_closure_set(v___f_365_, 2, v___y_352_);
lean_closure_set(v___f_365_, 3, v_acc_357_);
lean_closure_set(v___f_365_, 4, v_toBind_353_);
v_zero_370_ = lean_unsigned_to_nat(0u);
v_isZero_371_ = lean_nat_dec_eq(v_pos_361_, v_zero_370_);
if (v_isZero_371_ == 1)
{
lean_object* v___x_372_; 
lean_del_object(v___x_363_);
lean_dec(v_pos_361_);
lean_dec_ref(v_revComponents_360_);
v___x_372_ = lean_box(2);
v___y_367_ = v___x_372_;
goto v___jp_366_;
}
else
{
lean_object* v_one_373_; lean_object* v_n_374_; lean_object* v___x_376_; 
v_one_373_ = lean_unsigned_to_nat(1u);
v_n_374_ = lean_nat_sub(v_pos_361_, v_one_373_);
lean_dec(v_pos_361_);
lean_inc(v_n_374_);
lean_inc_ref(v_revComponents_360_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 1, v_n_374_);
v___x_376_ = v___x_363_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_revComponents_360_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_n_374_);
v___x_376_ = v_reuseFailAlloc_379_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_array_fget(v_revComponents_360_, v_n_374_);
lean_dec(v_n_374_);
lean_dec_ref(v_revComponents_360_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___y_367_ = v___x_378_;
goto v___jp_366_;
}
}
v___jp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_apply_2(v_toPure_354_, lean_box(0), v___y_367_);
v___x_369_ = lean_apply_4(v_lift_355_, lean_box(0), lean_box(0), v___f_365_, v___x_368_);
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object* v_inst_381_, lean_object* v_toPure_382_, lean_object* v_lift_383_, lean_object* v_00_u03b3_384_, lean_object* v_Pl_385_, lean_object* v_it_386_, lean_object* v_init_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_toApplicative_389_; lean_object* v_toBind_390_; lean_object* v_toPure_391_; lean_object* v___f_392_; lean_object* v___x_393_; 
v_toApplicative_389_ = lean_ctor_get(v_inst_381_, 0);
lean_inc_ref(v_toApplicative_389_);
v_toBind_390_ = lean_ctor_get(v_inst_381_, 1);
lean_inc(v_toBind_390_);
lean_dec_ref(v_inst_381_);
v_toPure_391_ = lean_ctor_get(v_toApplicative_389_, 1);
lean_inc(v_toPure_391_);
lean_dec_ref(v_toApplicative_389_);
v___f_392_ = lean_alloc_closure((void*)(l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__2), 9, 5);
lean_closure_set(v___f_392_, 0, v_toPure_391_);
lean_closure_set(v___f_392_, 1, v___y_388_);
lean_closure_set(v___f_392_, 2, v_toBind_390_);
lean_closure_set(v___f_392_, 3, v_toPure_382_);
lean_closure_set(v___f_392_, 4, v_lift_383_);
v___x_393_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_392_, v_it_386_, v_init_387_, lean_box(0));
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg(lean_object* v_inst_394_, lean_object* v_inst_395_){
_start:
{
lean_object* v_toApplicative_396_; lean_object* v_toPure_397_; lean_object* v___f_398_; 
v_toApplicative_396_ = lean_ctor_get(v_inst_394_, 0);
lean_inc_ref(v_toApplicative_396_);
lean_dec_ref(v_inst_394_);
v_toPure_397_ = lean_ctor_get(v_toApplicative_396_, 1);
lean_inc(v_toPure_397_);
lean_dec_ref(v_toApplicative_396_);
v___f_398_ = lean_alloc_closure((void*)(l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg___lam__3), 8, 2);
lean_closure_set(v___f_398_, 0, v_inst_395_);
lean_closure_set(v___f_398_, 1, v_toPure_397_);
return v___f_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad(lean_object* v_m_399_, lean_object* v_n_400_, lean_object* v_inst_401_, lean_object* v_inst_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Name_ComponentIterator_instIteratorLoopOfMonad___redArg(v_inst_401_, v_inst_402_);
return v___x_403_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_eqStr(lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_404_) == 1)
{
lean_object* v_pre_406_; 
v_pre_406_ = lean_ctor_get(v_x_404_, 0);
if (lean_obj_tag(v_pre_406_) == 0)
{
lean_object* v_str_407_; uint8_t v___x_408_; 
v_str_407_ = lean_ctor_get(v_x_404_, 1);
v___x_408_ = lean_string_dec_eq(v_str_407_, v_x_405_);
return v___x_408_;
}
else
{
uint8_t v___x_409_; 
v___x_409_ = 0;
return v___x_409_;
}
}
else
{
uint8_t v___x_410_; 
v___x_410_ = 0;
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eqStr___boxed(lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint8_t v_res_413_; lean_object* v_r_414_; 
v_res_413_ = l_Lean_Name_eqStr(v_x_411_, v_x_412_);
lean_dec_ref(v_x_412_);
lean_dec(v_x_411_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isPrefixOf(lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
uint8_t v___x_417_; 
v___x_417_ = lean_name_eq(v_x_415_, v_x_416_);
return v___x_417_;
}
else
{
lean_object* v_pre_418_; uint8_t v___x_419_; 
v_pre_418_ = lean_ctor_get(v_x_416_, 0);
v___x_419_ = lean_name_eq(v_x_415_, v_x_416_);
if (v___x_419_ == 0)
{
v_x_416_ = v_pre_418_;
goto _start;
}
else
{
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Lean_Name_isPrefixOf(v_x_421_, v_x_422_);
lean_dec(v_x_422_);
lean_dec(v_x_421_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isSuffixOf(lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
switch(lean_obj_tag(v_x_425_))
{
case 0:
{
uint8_t v___x_427_; 
v___x_427_ = 1;
return v___x_427_;
}
case 1:
{
if (lean_obj_tag(v_x_426_) == 1)
{
lean_object* v_pre_428_; lean_object* v_str_429_; lean_object* v_pre_430_; lean_object* v_str_431_; uint8_t v___x_432_; 
v_pre_428_ = lean_ctor_get(v_x_425_, 0);
v_str_429_ = lean_ctor_get(v_x_425_, 1);
v_pre_430_ = lean_ctor_get(v_x_426_, 0);
v_str_431_ = lean_ctor_get(v_x_426_, 1);
v___x_432_ = lean_string_dec_eq(v_str_429_, v_str_431_);
if (v___x_432_ == 0)
{
return v___x_432_;
}
else
{
v_x_425_ = v_pre_428_;
v_x_426_ = v_pre_430_;
goto _start;
}
}
else
{
uint8_t v___x_434_; 
v___x_434_ = 0;
return v___x_434_;
}
}
default: 
{
if (lean_obj_tag(v_x_426_) == 2)
{
lean_object* v_pre_435_; lean_object* v_i_436_; lean_object* v_pre_437_; lean_object* v_i_438_; uint8_t v___x_439_; 
v_pre_435_ = lean_ctor_get(v_x_425_, 0);
v_i_436_ = lean_ctor_get(v_x_425_, 1);
v_pre_437_ = lean_ctor_get(v_x_426_, 0);
v_i_438_ = lean_ctor_get(v_x_426_, 1);
v___x_439_ = lean_nat_dec_eq(v_i_436_, v_i_438_);
if (v___x_439_ == 0)
{
return v___x_439_;
}
else
{
v_x_425_ = v_pre_435_;
v_x_426_ = v_pre_437_;
goto _start;
}
}
else
{
uint8_t v___x_441_; 
v___x_441_ = 0;
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isSuffixOf___boxed(lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Lean_Name_isSuffixOf(v_x_442_, v_x_443_);
lean_dec(v_x_443_);
lean_dec(v_x_442_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_cmp(lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
switch(lean_obj_tag(v_x_446_))
{
case 0:
{
if (lean_obj_tag(v_x_447_) == 0)
{
uint8_t v___x_448_; 
v___x_448_ = 1;
return v___x_448_;
}
else
{
uint8_t v___x_449_; 
v___x_449_ = 0;
return v___x_449_;
}
}
case 1:
{
if (lean_obj_tag(v_x_447_) == 1)
{
lean_object* v_pre_450_; lean_object* v_str_451_; lean_object* v_pre_452_; lean_object* v_str_453_; uint8_t v___x_454_; 
v_pre_450_ = lean_ctor_get(v_x_446_, 0);
v_str_451_ = lean_ctor_get(v_x_446_, 1);
v_pre_452_ = lean_ctor_get(v_x_447_, 0);
v_str_453_ = lean_ctor_get(v_x_447_, 1);
v___x_454_ = l_Lean_Name_cmp(v_pre_450_, v_pre_452_);
if (v___x_454_ == 1)
{
uint8_t v___x_455_; 
v___x_455_ = lean_string_compare(v_str_451_, v_str_453_);
return v___x_455_;
}
else
{
return v___x_454_;
}
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 2;
return v___x_456_;
}
}
default: 
{
switch(lean_obj_tag(v_x_447_))
{
case 0:
{
uint8_t v___x_457_; 
v___x_457_ = 2;
return v___x_457_;
}
case 1:
{
uint8_t v___x_458_; 
v___x_458_ = 0;
return v___x_458_;
}
default: 
{
lean_object* v_pre_459_; lean_object* v_i_460_; lean_object* v_pre_461_; lean_object* v_i_462_; uint8_t v___x_463_; 
v_pre_459_ = lean_ctor_get(v_x_446_, 0);
v_i_460_ = lean_ctor_get(v_x_446_, 1);
v_pre_461_ = lean_ctor_get(v_x_447_, 0);
v_i_462_ = lean_ctor_get(v_x_447_, 1);
v___x_463_ = l_Lean_Name_cmp(v_pre_459_, v_pre_461_);
if (v___x_463_ == 1)
{
uint8_t v___x_464_; 
v___x_464_ = lean_nat_dec_lt(v_i_460_, v_i_462_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
v___x_465_ = lean_nat_dec_eq(v_i_460_, v_i_462_);
if (v___x_465_ == 0)
{
uint8_t v___x_466_; 
v___x_466_ = 2;
return v___x_466_;
}
else
{
return v___x_463_;
}
}
else
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
}
else
{
return v___x_463_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_cmp___boxed(lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Lean_Name_cmp(v_x_468_, v_x_469_);
lean_dec(v_x_469_);
lean_dec(v_x_468_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_lt(lean_object* v_x_472_, lean_object* v_y_473_){
_start:
{
uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_474_ = l_Lean_Name_cmp(v_x_472_, v_y_473_);
v___x_475_ = lean_box(v___x_474_);
v___x_476_ = lean_obj_tag_nat(v___x_475_);
lean_dec(v___x_475_);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_nat_dec_eq(v___x_476_, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_lt___boxed(lean_object* v_x_479_, lean_object* v_y_480_){
_start:
{
uint8_t v_res_481_; lean_object* v_r_482_; 
v_res_481_ = l_Lean_Name_lt(v_x_479_, v_y_480_);
lean_dec(v_y_480_);
lean_dec(v_x_479_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_quickCmpAux(lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
switch(lean_obj_tag(v_x_483_))
{
case 0:
{
if (lean_obj_tag(v_x_484_) == 0)
{
uint8_t v___x_485_; 
v___x_485_ = 1;
return v___x_485_;
}
else
{
uint8_t v___x_486_; 
v___x_486_ = 0;
return v___x_486_;
}
}
case 1:
{
if (lean_obj_tag(v_x_484_) == 1)
{
lean_object* v_pre_487_; lean_object* v_str_488_; lean_object* v_pre_489_; lean_object* v_str_490_; uint8_t v___x_491_; 
v_pre_487_ = lean_ctor_get(v_x_483_, 0);
v_str_488_ = lean_ctor_get(v_x_483_, 1);
v_pre_489_ = lean_ctor_get(v_x_484_, 0);
v_str_490_ = lean_ctor_get(v_x_484_, 1);
v___x_491_ = lean_string_compare(v_str_488_, v_str_490_);
if (v___x_491_ == 1)
{
v_x_483_ = v_pre_487_;
v_x_484_ = v_pre_489_;
goto _start;
}
else
{
return v___x_491_;
}
}
else
{
uint8_t v___x_493_; 
v___x_493_ = 2;
return v___x_493_;
}
}
default: 
{
switch(lean_obj_tag(v_x_484_))
{
case 0:
{
uint8_t v___x_494_; 
v___x_494_ = 2;
return v___x_494_;
}
case 1:
{
uint8_t v___x_495_; 
v___x_495_ = 0;
return v___x_495_;
}
default: 
{
lean_object* v_pre_496_; lean_object* v_i_497_; lean_object* v_pre_498_; lean_object* v_i_499_; uint8_t v___x_500_; 
v_pre_496_ = lean_ctor_get(v_x_483_, 0);
v_i_497_ = lean_ctor_get(v_x_483_, 1);
v_pre_498_ = lean_ctor_get(v_x_484_, 0);
v_i_499_ = lean_ctor_get(v_x_484_, 1);
v___x_500_ = lean_nat_dec_lt(v_i_497_, v_i_499_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
v___x_501_ = lean_nat_dec_eq(v_i_497_, v_i_499_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; 
v___x_502_ = 2;
return v___x_502_;
}
else
{
v_x_483_ = v_pre_496_;
v_x_484_ = v_pre_498_;
goto _start;
}
}
else
{
uint8_t v___x_504_; 
v___x_504_ = 0;
return v___x_504_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_quickCmpAux___boxed(lean_object* v_x_505_, lean_object* v_x_506_){
_start:
{
uint8_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = l_Lean_Name_quickCmpAux(v_x_505_, v_x_506_);
lean_dec(v_x_506_);
lean_dec(v_x_505_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(lean_object* v_n_u2081_509_, lean_object* v_n_u2082_510_){
_start:
{
size_t v___x_511_; size_t v___x_512_; uint8_t v___x_513_; 
v___x_511_ = lean_ptr_addr(v_n_u2081_509_);
v___x_512_ = lean_ptr_addr(v_n_u2082_510_);
v___x_513_ = lean_usize_dec_eq(v___x_511_, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1___boxed(lean_object* v_n_u2081_514_, lean_object* v_n_u2082_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(v_n_u2081_514_, v_n_u2082_515_);
lean_dec(v_n_u2082_515_);
lean_dec(v_n_u2081_514_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object* v_n_u2081_518_, lean_object* v_n_u2082_519_){
_start:
{
uint64_t v___y_521_; uint64_t v___y_522_; uint64_t v___y_529_; size_t v___x_532_; size_t v___x_533_; uint8_t v___x_534_; 
v___x_532_ = lean_ptr_addr(v_n_u2081_518_);
v___x_533_ = lean_ptr_addr(v_n_u2082_519_);
v___x_534_ = lean_usize_dec_eq(v___x_532_, v___x_533_);
if (v___x_534_ == 0)
{
if (lean_obj_tag(v_n_u2081_518_) == 0)
{
uint64_t v___x_535_; 
v___x_535_ = 1723ULL;
v___y_529_ = v___x_535_;
goto v___jp_528_;
}
else
{
uint64_t v_hash_536_; 
v_hash_536_ = lean_ctor_get_uint64(v_n_u2081_518_, sizeof(void*)*2);
v___y_529_ = v_hash_536_;
goto v___jp_528_;
}
}
else
{
uint8_t v___x_537_; 
v___x_537_ = 1;
return v___x_537_;
}
v___jp_520_:
{
uint8_t v___x_523_; 
v___x_523_ = lean_uint64_dec_lt(v___y_521_, v___y_522_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; 
v___x_524_ = lean_uint64_dec_eq(v___y_521_, v___y_522_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; 
v___x_525_ = 2;
return v___x_525_;
}
else
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Name_quickCmpAux(v_n_u2081_518_, v_n_u2082_519_);
return v___x_526_;
}
}
else
{
uint8_t v___x_527_; 
v___x_527_ = 0;
return v___x_527_;
}
}
v___jp_528_:
{
if (lean_obj_tag(v_n_u2082_519_) == 0)
{
uint64_t v___x_530_; 
v___x_530_ = 1723ULL;
v___y_521_ = v___y_529_;
v___y_522_ = v___x_530_;
goto v___jp_520_;
}
else
{
uint64_t v_hash_531_; 
v_hash_531_ = lean_ctor_get_uint64(v_n_u2082_519_, sizeof(void*)*2);
v___y_521_ = v___y_529_;
v___y_522_ = v_hash_531_;
goto v___jp_520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object* v_n_u2081_538_, lean_object* v_n_u2082_539_){
_start:
{
uint8_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_538_, v_n_u2082_539_);
lean_dec(v_n_u2082_539_);
lean_dec(v_n_u2081_538_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_quickLt(lean_object* v_n_u2081_542_, lean_object* v_n_u2082_543_){
_start:
{
uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_544_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_542_, v_n_u2082_543_);
v___x_545_ = lean_box(v___x_544_);
v___x_546_ = lean_obj_tag_nat(v___x_545_);
lean_dec(v___x_545_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_nat_dec_eq(v___x_546_, v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_quickLt___boxed(lean_object* v_n_u2081_549_, lean_object* v_n_u2082_550_){
_start:
{
uint8_t v_res_551_; lean_object* v_r_552_; 
v_res_551_ = l_Lean_Name_quickLt(v_n_u2081_549_, v_n_u2082_550_);
lean_dec(v_n_u2082_550_);
lean_dec(v_n_u2081_549_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternal(lean_object* v_x_553_){
_start:
{
switch(lean_obj_tag(v_x_553_))
{
case 1:
{
lean_object* v_pre_554_; lean_object* v_str_555_; uint32_t v___y_557_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_pre_554_ = lean_ctor_get(v_x_553_, 0);
v_str_555_ = lean_ctor_get(v_x_553_, 1);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_string_utf8_byte_size(v_str_555_);
lean_inc_ref(v_str_555_);
v___x_563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_563_, 0, v_str_555_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
lean_ctor_set(v___x_563_, 2, v___x_562_);
v___x_564_ = l_String_Slice_Pos_get_x3f(v___x_563_, v___x_561_);
lean_dec_ref_known(v___x_563_, 3);
if (lean_obj_tag(v___x_564_) == 0)
{
uint32_t v___x_565_; 
v___x_565_ = 65;
v___y_557_ = v___x_565_;
goto v___jp_556_;
}
else
{
lean_object* v_val_566_; uint32_t v___x_567_; 
v_val_566_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_566_);
lean_dec_ref_known(v___x_564_, 1);
v___x_567_ = lean_unbox_uint32(v_val_566_);
lean_dec(v_val_566_);
v___y_557_ = v___x_567_;
goto v___jp_556_;
}
v___jp_556_:
{
uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 95;
v___x_559_ = lean_uint32_dec_eq(v___y_557_, v___x_558_);
if (v___x_559_ == 0)
{
v_x_553_ = v_pre_554_;
goto _start;
}
else
{
return v___x_559_;
}
}
}
case 2:
{
lean_object* v_pre_568_; 
v_pre_568_ = lean_ctor_get(v_x_553_, 0);
v_x_553_ = v_pre_568_;
goto _start;
}
default: 
{
uint8_t v___x_570_; 
v___x_570_ = 0;
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternal___boxed(lean_object* v_x_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Lean_Name_isInternal(v_x_571_);
lean_dec(v_x_571_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternalOrNum(lean_object* v_x_574_){
_start:
{
switch(lean_obj_tag(v_x_574_))
{
case 1:
{
lean_object* v_pre_575_; lean_object* v_str_576_; uint32_t v___y_578_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_pre_575_ = lean_ctor_get(v_x_574_, 0);
v_str_576_ = lean_ctor_get(v_x_574_, 1);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_string_utf8_byte_size(v_str_576_);
lean_inc_ref(v_str_576_);
v___x_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_584_, 0, v_str_576_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
lean_ctor_set(v___x_584_, 2, v___x_583_);
v___x_585_ = l_String_Slice_Pos_get_x3f(v___x_584_, v___x_582_);
lean_dec_ref_known(v___x_584_, 3);
if (lean_obj_tag(v___x_585_) == 0)
{
uint32_t v___x_586_; 
v___x_586_ = 65;
v___y_578_ = v___x_586_;
goto v___jp_577_;
}
else
{
lean_object* v_val_587_; uint32_t v___x_588_; 
v_val_587_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v___x_585_, 1);
v___x_588_ = lean_unbox_uint32(v_val_587_);
lean_dec(v_val_587_);
v___y_578_ = v___x_588_;
goto v___jp_577_;
}
v___jp_577_:
{
uint32_t v___x_579_; uint8_t v___x_580_; 
v___x_579_ = 95;
v___x_580_ = lean_uint32_dec_eq(v___y_578_, v___x_579_);
if (v___x_580_ == 0)
{
v_x_574_ = v_pre_575_;
goto _start;
}
else
{
return v___x_580_;
}
}
}
case 2:
{
uint8_t v___x_589_; 
v___x_589_ = 1;
return v___x_589_;
}
default: 
{
uint8_t v___x_590_; 
v___x_590_ = 0;
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalOrNum___boxed(lean_object* v_x_591_){
_start:
{
uint8_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_Lean_Name_isInternalOrNum(v_x_591_);
lean_dec(v_x_591_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(lean_object* v_pre_594_, lean_object* v_s_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_596_ = lean_string_utf8_byte_size(v_s_595_);
v___x_597_ = lean_string_utf8_byte_size(v_pre_594_);
v___x_598_ = lean_nat_dec_le(v___x_597_, v___x_596_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
lean_dec_ref(v_s_595_);
v___x_599_ = lean_box(0);
return v___x_599_;
}
else
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_string_memcmp(v_s_595_, v_pre_594_, v___x_600_, v___x_600_, v___x_597_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec_ref(v_s_595_);
v___x_602_ = lean_box(0);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_inc_ref(v_s_595_);
v___x_603_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_603_, 0, v_s_595_);
lean_ctor_set(v___x_603_, 1, v___x_600_);
lean_ctor_set(v___x_603_, 2, v___x_596_);
v___x_604_ = l_String_Slice_pos_x21(v___x_603_, v___x_597_);
lean_dec_ref_known(v___x_603_, 3);
v___x_605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_605_, 0, v_s_595_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
lean_ctor_set(v___x_605_, 2, v___x_596_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg___boxed(lean_object* v_pre_607_, lean_object* v_s_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_607_, v_s_608_);
lean_dec_ref(v_pre_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(lean_object* v_pre_610_, lean_object* v_s_611_, lean_object* v_pat_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_610_, v_s_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(lean_object* v_pre_614_, lean_object* v_s_615_, lean_object* v_pat_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(v_pre_614_, v_s_615_, v_pat_616_);
lean_dec_ref(v_pat_616_);
lean_dec_ref(v_pre_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(lean_object* v_s_618_, lean_object* v_pos_619_){
_start:
{
lean_object* v_str_620_; lean_object* v_startInclusive_621_; lean_object* v_endExclusive_622_; lean_object* v___x_623_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v_decide_634_; 
v_str_620_ = lean_ctor_get(v_s_618_, 0);
v_startInclusive_621_ = lean_ctor_get(v_s_618_, 1);
v_endExclusive_622_ = lean_ctor_get(v_s_618_, 2);
v___x_623_ = lean_nat_add(v_startInclusive_621_, v_pos_619_);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_nat_sub(v_endExclusive_622_, v___x_623_);
v_decide_634_ = lean_nat_dec_eq(v___x_632_, v___x_633_);
lean_dec(v___x_633_);
if (v_decide_634_ == 0)
{
uint32_t v___x_635_; uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_635_ = lean_string_utf8_get_fast(v_str_620_, v___x_623_);
v___x_639_ = 48;
v___x_640_ = lean_uint32_dec_le(v___x_639_, v___x_635_);
if (v___x_640_ == 0)
{
goto v___jp_636_;
}
else
{
uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 57;
v___x_642_ = lean_uint32_dec_le(v___x_635_, v___x_641_);
if (v___x_642_ == 0)
{
goto v___jp_636_;
}
else
{
goto v___jp_624_;
}
}
v___jp_636_:
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 95;
v___x_638_ = lean_uint32_dec_eq(v___x_635_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec(v___x_623_);
return v_pos_619_;
}
else
{
goto v___jp_624_;
}
}
}
else
{
lean_dec(v___x_623_);
return v_pos_619_;
}
v___jp_624_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_625_ = lean_string_utf8_next_fast(v_str_620_, v___x_623_);
v___x_626_ = lean_nat_sub(v___x_625_, v___x_623_);
lean_dec(v___x_623_);
v___x_627_ = lean_nat_add(v_pos_619_, v___x_626_);
lean_dec(v___x_626_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_pos_619_, v___x_628_);
v___x_630_ = lean_nat_dec_le(v___x_629_, v___x_627_);
lean_dec(v___x_629_);
if (v___x_630_ == 0)
{
lean_dec(v___x_627_);
return v_pos_619_;
}
else
{
lean_dec(v_pos_619_);
v_pos_619_ = v___x_627_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1___boxed(lean_object* v_s_643_, lean_object* v_pos_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(v_s_643_, v_pos_644_);
lean_dec_ref(v_s_643_);
return v_res_645_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(lean_object* v_s_646_, lean_object* v_pre_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_647_, v_s_646_);
if (lean_obj_tag(v___x_648_) == 0)
{
uint8_t v___x_649_; 
v___x_649_ = 0;
return v___x_649_;
}
else
{
lean_object* v_val_650_; lean_object* v_startInclusive_651_; lean_object* v_endExclusive_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v_decide_656_; 
v_val_650_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v___x_648_, 1);
v_startInclusive_651_ = lean_ctor_get(v_val_650_, 1);
lean_inc(v_startInclusive_651_);
v_endExclusive_652_ = lean_ctor_get(v_val_650_, 2);
lean_inc(v_endExclusive_652_);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(v_val_650_, v___x_653_);
lean_dec(v_val_650_);
v___x_655_ = lean_nat_sub(v_endExclusive_652_, v_startInclusive_651_);
lean_dec(v_startInclusive_651_);
lean_dec(v_endExclusive_652_);
v_decide_656_ = lean_nat_dec_eq(v___x_654_, v___x_655_);
lean_dec(v___x_655_);
lean_dec(v___x_654_);
return v_decide_656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix___boxed(lean_object* v_s_657_, lean_object* v_pre_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_s_657_, v_pre_658_);
lean_dec_ref(v_pre_658_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInternalDetail(lean_object* v_x_666_){
_start:
{
switch(lean_obj_tag(v_x_666_))
{
case 1:
{
lean_object* v_pre_667_; lean_object* v_str_668_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_pre_667_ = lean_ctor_get(v_x_666_, 0);
lean_inc(v_pre_667_);
v_str_668_ = lean_ctor_get(v_x_666_, 1);
lean_inc_ref(v_str_668_);
lean_dec_ref_known(v_x_666_, 2);
v___x_679_ = lean_string_utf8_byte_size(v_str_668_);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_dec_le(v___x_680_, v___x_679_);
if (v___x_681_ == 0)
{
goto v___jp_669_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_682_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__4));
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_string_memcmp(v_str_668_, v___x_682_, v___x_683_, v___x_683_, v___x_680_);
if (v___x_684_ == 0)
{
goto v___jp_669_;
}
else
{
lean_dec_ref(v_str_668_);
lean_dec(v_pre_667_);
return v___x_684_;
}
}
v___jp_669_:
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__0));
lean_inc_ref(v_str_668_);
v___x_671_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_668_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__1));
lean_inc_ref(v_str_668_);
v___x_673_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_668_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__2));
lean_inc_ref(v_str_668_);
v___x_675_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_668_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_Name_isInternalDetail___closed__3));
v___x_677_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_668_, v___x_676_);
if (v___x_677_ == 0)
{
uint8_t v___x_678_; 
v___x_678_ = l_Lean_Name_isInternalOrNum(v_pre_667_);
lean_dec(v_pre_667_);
return v___x_678_;
}
else
{
lean_dec(v_pre_667_);
return v___x_677_;
}
}
else
{
lean_dec_ref(v_str_668_);
lean_dec(v_pre_667_);
return v___x_675_;
}
}
else
{
lean_dec_ref(v_str_668_);
lean_dec(v_pre_667_);
return v___x_673_;
}
}
else
{
lean_dec_ref(v_str_668_);
lean_dec(v_pre_667_);
return v___x_671_;
}
}
}
case 2:
{
uint8_t v___x_685_; 
lean_dec_ref_known(v_x_666_, 2);
v___x_685_ = 1;
return v___x_685_;
}
default: 
{
uint8_t v___x_686_; 
v___x_686_ = l_Lean_Name_isInternalOrNum(v_x_666_);
lean_dec(v_x_666_);
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInternalDetail___boxed(lean_object* v_x_687_){
_start:
{
uint8_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_Lean_Name_isInternalDetail(v_x_687_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isImplementationDetail(lean_object* v_x_691_){
_start:
{
switch(lean_obj_tag(v_x_691_))
{
case 0:
{
uint8_t v___x_692_; 
v___x_692_ = 0;
return v___x_692_;
}
case 1:
{
lean_object* v_pre_693_; 
v_pre_693_ = lean_ctor_get(v_x_691_, 0);
if (lean_obj_tag(v_pre_693_) == 0)
{
lean_object* v_str_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_str_694_ = lean_ctor_get(v_x_691_, 1);
v___x_695_ = lean_string_utf8_byte_size(v_str_694_);
v___x_696_ = lean_unsigned_to_nat(2u);
v___x_697_ = lean_nat_dec_le(v___x_696_, v___x_695_);
if (v___x_697_ == 0)
{
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = ((lean_object*)(l_Lean_Name_isImplementationDetail___closed__0));
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_string_memcmp(v_str_694_, v___x_698_, v___x_699_, v___x_699_, v___x_696_);
return v___x_700_;
}
}
else
{
v_x_691_ = v_pre_693_;
goto _start;
}
}
default: 
{
lean_object* v_pre_702_; 
v_pre_702_ = lean_ctor_get(v_x_691_, 0);
v_x_691_ = v_pre_702_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isImplementationDetail___boxed(lean_object* v_x_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_Lean_Name_isImplementationDetail(v_x_704_);
lean_dec(v_x_704_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isAtomic(lean_object* v_x_707_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
uint8_t v___x_708_; 
v___x_708_ = 1;
return v___x_708_;
}
else
{
lean_object* v_pre_709_; 
v_pre_709_ = lean_ctor_get(v_x_707_, 0);
if (lean_obj_tag(v_pre_709_) == 0)
{
uint8_t v___x_710_; 
v___x_710_ = 1;
return v___x_710_;
}
else
{
uint8_t v___x_711_; 
v___x_711_ = 0;
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isAtomic___boxed(lean_object* v_x_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_Lean_Name_isAtomic(v_x_712_);
lean_dec(v_x_712_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_hasSingleComponent(lean_object* v_x_715_){
_start:
{
switch(lean_obj_tag(v_x_715_))
{
case 1:
{
lean_object* v_pre_716_; 
v_pre_716_ = lean_ctor_get(v_x_715_, 0);
if (lean_obj_tag(v_pre_716_) == 0)
{
uint8_t v___x_717_; 
v___x_717_ = 1;
return v___x_717_;
}
else
{
uint8_t v___x_718_; 
v___x_718_ = 0;
return v___x_718_;
}
}
case 2:
{
lean_object* v_pre_719_; 
v_pre_719_ = lean_ctor_get(v_x_715_, 0);
if (lean_obj_tag(v_pre_719_) == 0)
{
uint8_t v___x_720_; 
v___x_720_ = 1;
return v___x_720_;
}
else
{
uint8_t v___x_721_; 
v___x_721_ = 0;
return v___x_721_;
}
}
default: 
{
uint8_t v___x_722_; 
v___x_722_ = 0;
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_hasSingleComponent___boxed(lean_object* v_x_723_){
_start:
{
uint8_t v_res_724_; lean_object* v_r_725_; 
v_res_724_ = l_Lean_Name_hasSingleComponent(v_x_723_);
lean_dec(v_x_723_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isAnonymous(lean_object* v_x_726_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
uint8_t v___x_727_; 
v___x_727_ = 1;
return v___x_727_;
}
else
{
uint8_t v___x_728_; 
v___x_728_ = 0;
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isAnonymous___boxed(lean_object* v_x_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l_Lean_Name_isAnonymous(v_x_729_);
lean_dec(v_x_729_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isStr(lean_object* v_x_732_){
_start:
{
if (lean_obj_tag(v_x_732_) == 1)
{
uint8_t v___x_733_; 
v___x_733_ = 1;
return v___x_733_;
}
else
{
uint8_t v___x_734_; 
v___x_734_ = 0;
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isStr___boxed(lean_object* v_x_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l_Lean_Name_isStr(v_x_735_);
lean_dec(v_x_735_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isNum(lean_object* v_x_738_){
_start:
{
if (lean_obj_tag(v_x_738_) == 2)
{
uint8_t v___x_739_; 
v___x_739_ = 1;
return v___x_739_;
}
else
{
uint8_t v___x_740_; 
v___x_740_ = 0;
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isNum___boxed(lean_object* v_x_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l_Lean_Name_isNum(v_x_741_);
lean_dec(v_x_741_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_anyS(lean_object* v_n_744_, lean_object* v_f_745_){
_start:
{
switch(lean_obj_tag(v_n_744_))
{
case 1:
{
lean_object* v_pre_746_; lean_object* v_str_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_pre_746_ = lean_ctor_get(v_n_744_, 0);
lean_inc(v_pre_746_);
v_str_747_ = lean_ctor_get(v_n_744_, 1);
lean_inc_ref(v_str_747_);
lean_dec_ref_known(v_n_744_, 2);
lean_inc_ref(v_f_745_);
v___x_748_ = lean_apply_1(v_f_745_, v_str_747_);
v___x_749_ = lean_unbox(v___x_748_);
if (v___x_749_ == 0)
{
v_n_744_ = v_pre_746_;
goto _start;
}
else
{
uint8_t v___x_751_; 
lean_dec(v_pre_746_);
lean_dec_ref(v_f_745_);
v___x_751_ = lean_unbox(v___x_748_);
return v___x_751_;
}
}
case 2:
{
lean_object* v_pre_752_; 
v_pre_752_ = lean_ctor_get(v_n_744_, 0);
lean_inc(v_pre_752_);
lean_dec_ref_known(v_n_744_, 2);
v_n_744_ = v_pre_752_;
goto _start;
}
default: 
{
uint8_t v___x_754_; 
lean_dec_ref(v_f_745_);
lean_dec(v_n_744_);
v___x_754_ = 0;
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_anyS___boxed(lean_object* v_n_755_, lean_object* v_f_756_){
_start:
{
uint8_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l_Lean_Name_anyS(v_n_755_, v_f_756_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg(uint8_t v___x_763_, lean_object* v_a_764_, uint8_t v_b_765_){
_start:
{
lean_object* v_it_767_; lean_object* v_out_768_; 
switch(lean_obj_tag(v_a_764_))
{
case 0:
{
return v_b_765_;
}
case 1:
{
lean_object* v_pre_782_; lean_object* v_str_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_pre_782_ = lean_ctor_get(v_a_764_, 0);
lean_inc(v_pre_782_);
v_str_783_ = lean_ctor_get(v_a_764_, 1);
lean_inc_ref(v_str_783_);
lean_dec_ref_known(v_a_764_, 2);
v___x_784_ = lean_box(0);
v___x_785_ = l_Lean_Name_str___override(v___x_784_, v_str_783_);
v_it_767_ = v_pre_782_;
v_out_768_ = v___x_785_;
goto v___jp_766_;
}
default: 
{
lean_object* v_pre_786_; lean_object* v_i_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_pre_786_ = lean_ctor_get(v_a_764_, 0);
lean_inc(v_pre_786_);
v_i_787_ = lean_ctor_get(v_a_764_, 1);
lean_inc(v_i_787_);
lean_dec_ref_known(v_a_764_, 2);
v___x_788_ = lean_box(0);
v___x_789_ = l_Lean_Name_num___override(v___x_788_, v_i_787_);
v_it_767_ = v_pre_786_;
v_out_768_ = v___x_789_;
goto v___jp_766_;
}
}
v___jp_766_:
{
if (lean_obj_tag(v_out_768_) == 1)
{
lean_object* v_pre_769_; 
v_pre_769_ = lean_ctor_get(v_out_768_, 0);
if (lean_obj_tag(v_pre_769_) == 0)
{
lean_object* v_str_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v_str_770_ = lean_ctor_get(v_out_768_, 1);
lean_inc_ref(v_str_770_);
lean_dec_ref_known(v_out_768_, 2);
v___x_771_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__0));
v___x_772_ = lean_string_dec_eq(v_str_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__1));
v___x_774_ = lean_string_dec_eq(v_str_770_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__2));
v___x_776_ = lean_string_dec_eq(v_str_770_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___closed__3));
v___x_778_ = lean_string_dec_eq(v_str_770_, v___x_777_);
lean_dec_ref(v_str_770_);
if (v___x_778_ == 0)
{
{
lean_object* _tmp_1 = v_it_767_;
uint8_t _tmp_2 = v___x_763_;
v_a_764_ = _tmp_1;
v_b_765_ = _tmp_2;
}
goto _start;
}
else
{
lean_dec(v_it_767_);
return v___x_778_;
}
}
else
{
lean_dec_ref(v_str_770_);
lean_dec(v_it_767_);
return v___x_776_;
}
}
else
{
lean_dec_ref(v_str_770_);
lean_dec(v_it_767_);
return v___x_774_;
}
}
else
{
lean_dec_ref(v_str_770_);
lean_dec(v_it_767_);
return v___x_772_;
}
}
else
{
lean_dec_ref_known(v_out_768_, 2);
{
lean_object* _tmp_1 = v_it_767_;
uint8_t _tmp_2 = v___x_763_;
v_a_764_ = _tmp_1;
v_b_765_ = _tmp_2;
}
goto _start;
}
}
else
{
lean_dec(v_out_768_);
{
lean_object* _tmp_1 = v_it_767_;
uint8_t _tmp_2 = v___x_763_;
v_a_764_ = _tmp_1;
v_b_765_ = _tmp_2;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg___boxed(lean_object* v___x_790_, lean_object* v_a_791_, lean_object* v_b_792_){
_start:
{
uint8_t v___x_664__boxed_793_; uint8_t v_b_boxed_794_; uint8_t v_res_795_; lean_object* v_r_796_; 
v___x_664__boxed_793_ = lean_unbox(v___x_790_);
v_b_boxed_794_ = lean_unbox(v_b_792_);
v_res_795_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg(v___x_664__boxed_793_, v_a_791_, v_b_boxed_794_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isMetaprogramming(lean_object* v_n_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_801_ = l_Lean_Name_getRoot(v_n_800_);
v___x_802_ = ((lean_object*)(l_Lean_Name_isMetaprogramming___closed__1));
v___x_803_ = lean_name_eq(v___x_801_, v___x_802_);
lean_dec(v___x_801_);
if (v___x_803_ == 0)
{
uint8_t v___x_804_; 
v___x_804_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg(v___x_803_, v_n_800_, v___x_803_);
return v___x_804_;
}
else
{
lean_dec(v_n_800_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isMetaprogramming___boxed(lean_object* v_n_805_){
_start:
{
uint8_t v_res_806_; lean_object* v_r_807_; 
v_res_806_ = l_Lean_Name_isMetaprogramming(v_n_805_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0(uint8_t v___x_808_, lean_object* v_inst_809_, lean_object* v_R_810_, lean_object* v_a_811_, uint8_t v_b_812_, lean_object* v_c_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___redArg(v___x_808_, v_a_811_, v_b_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0___boxed(lean_object* v___x_815_, lean_object* v_inst_816_, lean_object* v_R_817_, lean_object* v_a_818_, lean_object* v_b_819_, lean_object* v_c_820_){
_start:
{
uint8_t v___x_736__boxed_821_; uint8_t v_b_boxed_822_; uint8_t v_res_823_; lean_object* v_r_824_; 
v___x_736__boxed_821_ = lean_unbox(v___x_815_);
v_b_boxed_822_ = lean_unbox(v_b_819_);
v_res_823_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Name_isMetaprogramming_spec__0(v___x_736__boxed_821_, v_inst_816_, v_R_817_, v_a_818_, v_b_boxed_822_, v_c_820_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Name_instInhabitedRevComponentIterator_default = _init_l_Lean_Name_instInhabitedRevComponentIterator_default();
lean_mark_persistent(l_Lean_Name_instInhabitedRevComponentIterator_default);
l_Lean_Name_instInhabitedRevComponentIterator = _init_l_Lean_Name_instInhabitedRevComponentIterator();
lean_mark_persistent(l_Lean_Name_instInhabitedRevComponentIterator);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Name(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_String(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Name(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Name(builtin);
}
#ifdef __cplusplus
}
#endif
