// Lean compiler output
// Module: Lake.Config.Artifact
// Imports: public import Lake.Build.Trace
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
lean_object* lean_nat_to_int(lean_object*);
extern uint64_t l_Lake_Hash_nil;
lean_object* l_Lake_instReprHash_repr___redArg(uint64_t);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofHex_x3f(lean_object*);
lean_object* l_Lake_lowerHexUInt64(uint64_t);
static const lean_string_object l_Lake_artifactPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_artifactPath___closed__0 = (const lean_object*)&l_Lake_artifactPath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_artifactPath(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_artifactPath___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedArtifactDescr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "art"};
static const lean_object* l_Lake_instInhabitedArtifactDescr_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedArtifactDescr_default___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedArtifactDescr_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedArtifactDescr_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedArtifactDescr_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedArtifactDescr;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprArtifactDescr_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hash"};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprArtifactDescr_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__9_value;
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lake_instReprArtifactDescr_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__12;
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lake_instReprArtifactDescr_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__14;
static lean_once_cell_t l_Lake_instReprArtifactDescr_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__15;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__16 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__13_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprArtifactDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprArtifactDescr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprArtifactDescr___closed__0 = (const lean_object*)&l_Lake_instReprArtifactDescr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprArtifactDescr = (const lean_object*)&l_Lake_instReprArtifactDescr___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_artifactWithExt(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_artifactWithExt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_relPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_relPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_ArtifactDescr_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ArtifactDescr_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ArtifactDescr_instToString___closed__0 = (const lean_object*)&l_Lake_ArtifactDescr_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ArtifactDescr_instToString = (const lean_object*)&l_Lake_ArtifactDescr_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToJson___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToJson___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_ArtifactDescr_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ArtifactDescr_instToJson___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ArtifactDescr_instToJson___closed__0 = (const lean_object*)&l_Lake_ArtifactDescr_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ArtifactDescr_instToJson = (const lean_object*)&l_Lake_ArtifactDescr_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "expected artifact file name to be a content hash"};
static const lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0 = (const lean_object*)&l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0_value;
static const lean_ctor_object l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0_value)}};
static const lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1 = (const lean_object*)&l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1_value;
static const lean_string_object l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2 = (const lean_object*)&l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ArtifactDescr_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "artifact in unexpected JSON format: "};
static const lean_object* l_Lake_ArtifactDescr_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_ArtifactDescr_fromJson_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_ArtifactDescr_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ArtifactDescr_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ArtifactDescr_instFromJson___closed__0 = (const lean_object*)&l_Lake_ArtifactDescr_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ArtifactDescr_instFromJson = (const lean_object*)&l_Lake_ArtifactDescr_instFromJson___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedArtifact_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedArtifact_default___closed__0;
static lean_once_cell_t l_Lake_instInhabitedArtifact_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedArtifact_default___closed__1;
static lean_once_cell_t l_Lake_instInhabitedArtifact_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedArtifact_default___closed__2;
LEAN_EXPORT lean_object* l_Lake_instInhabitedArtifact_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedArtifact;
static const lean_string_object l_Lake_instReprArtifact_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "descr"};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprArtifact_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprArtifact_repr___redArg___closed__4;
static const lean_string_object l_Lake_instReprArtifact_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__6_value;
static const lean_string_object l_Lake_instReprArtifact_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__7 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__7_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__8_value;
static const lean_string_object l_Lake_instReprArtifact_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__9_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__10_value;
static const lean_string_object l_Lake_instReprArtifact_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mtime"};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__11_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprArtifact_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprArtifact___closed__0 = (const lean_object*)&l_Lake_instReprArtifact___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprArtifact = (const lean_object*)&l_Lake_instReprArtifact___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Artifact_withName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Artifact_useLocalFile(lean_object*, lean_object*);
static const lean_array_object l_Lake_Artifact_trace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Artifact_trace___closed__0 = (const lean_object*)&l_Lake_Artifact_trace___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Artifact_trace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Artifact_trace___boxed(lean_object*);
lean_object* l_Lake_artifactPath(uint64_t v_contentHash_2_, lean_object* v_ext_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_4_ = lean_string_utf8_byte_size(v_ext_3_);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_nat_dec_eq(v___x_4_, v___x_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = l_Lake_lowerHexUInt64(v_contentHash_2_);
v___x_8_ = ((lean_object*)(l_Lake_artifactPath___closed__0));
v___x_9_ = lean_string_append(v___x_7_, v___x_8_);
v___x_10_ = lean_string_append(v___x_9_, v_ext_3_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
v___x_11_ = l_Lake_lowerHexUInt64(v_contentHash_2_);
return v___x_11_;
}
}
}
LEAN_EXPORT void l_Lake_artifactPath_0interp(lean_interpreter_value* stack)
{
uint64_t v_contentHash_2_ = stack[0].m_num;
lean_object* v_ext_3_ = stack[1].m_obj;
lean_object* v_res_12_;
v_res_12_ = l_Lake_artifactPath(v_contentHash_2_, v_ext_3_);
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_Lake_artifactPath___boxed(lean_object* v_contentHash_13_, lean_object* v_ext_14_){
_start:
{
uint64_t v_contentHash_boxed_15_; lean_object* v_res_16_; 
v_contentHash_boxed_15_ = lean_unbox_uint64(v_contentHash_13_);
lean_dec_ref(v_contentHash_13_);
v_res_16_ = l_Lake_artifactPath(v_contentHash_boxed_15_, v_ext_14_);
lean_dec_ref(v_ext_14_);
return v_res_16_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifactDescr_default___closed__1(void){
_start:
{
lean_object* v___x_18_; uint64_t v___x_19_; lean_object* v___x_20_; 
v___x_18_ = ((lean_object*)(l_Lake_instInhabitedArtifactDescr_default___closed__0));
v___x_19_ = l_Lake_Hash_nil;
v___x_20_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_20_, 0, v___x_18_);
lean_ctor_set_uint64(v___x_20_, sizeof(void*)*1, v___x_19_);
return v___x_20_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifactDescr_default(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Lake_instInhabitedArtifactDescr_default___closed__1, &l_Lake_instInhabitedArtifactDescr_default___closed__1_once, _init_l_Lake_instInhabitedArtifactDescr_default___closed__1);
return v___x_21_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifactDescr(void){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lake_instInhabitedArtifactDescr_default;
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprArtifactDescr_repr_spec__0(lean_object* v_a_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_nat_to_int(v_a_23_);
return v___x_24_;
}
}
static lean_object* _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(8u);
v___x_39_ = lean_nat_to_int(v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(7u);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__0));
v___x_50_ = lean_string_length(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__14, &l_Lake_instReprArtifactDescr_repr___redArg___closed__14_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__14);
v___x_52_ = lean_nat_to_int(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr___redArg(lean_object* v_x_57_){
_start:
{
uint64_t v_hash_58_; lean_object* v_ext_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_hash_58_ = lean_ctor_get_uint64(v_x_57_, sizeof(void*)*1);
v_ext_59_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_ext_59_);
lean_dec_ref(v_x_57_);
v___x_60_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__5));
v___x_61_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__6));
v___x_62_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__7, &l_Lake_instReprArtifactDescr_repr___redArg___closed__7_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__7);
v___x_63_ = l_Lake_instReprHash_repr___redArg(v_hash_58_);
v___x_64_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = 0;
v___x_66_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set_uint8(v___x_66_, sizeof(void*)*1, v___x_65_);
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_61_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__9));
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_box(1);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__11));
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_60_);
v___x_75_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__12, &l_Lake_instReprArtifactDescr_repr___redArg___closed__12_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__12);
v___x_76_ = l_String_quote(v_ext_59_);
v___x_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
v___x_78_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_75_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*1, v___x_65_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_74_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__15, &l_Lake_instReprArtifactDescr_repr___redArg___closed__15_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__15);
v___x_82_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__16));
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_80_);
v___x_84_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__17));
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_81_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_65_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr(lean_object* v_x_88_, lean_object* v_prec_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lake_instReprArtifactDescr_repr___redArg(v_x_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr___boxed(lean_object* v_x_91_, lean_object* v_prec_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lake_instReprArtifactDescr_repr(v_x_91_, v_prec_92_);
lean_dec(v_prec_92_);
return v_res_93_;
}
}
lean_object* l_Lake_artifactWithExt(uint64_t v_contentHash_96_, lean_object* v_ext_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_98_, 0, v_ext_97_);
lean_ctor_set_uint64(v___x_98_, sizeof(void*)*1, v_contentHash_96_);
return v___x_98_;
}
}
LEAN_EXPORT void l_Lake_artifactWithExt_0interp(lean_interpreter_value* stack)
{
uint64_t v_contentHash_96_ = stack[0].m_num;
lean_object* v_ext_97_ = stack[1].m_obj;
lean_object* v_res_99_;
v_res_99_ = l_Lake_artifactWithExt(v_contentHash_96_, v_ext_97_);
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l_Lake_artifactWithExt___boxed(lean_object* v_contentHash_100_, lean_object* v_ext_101_){
_start:
{
uint64_t v_contentHash_boxed_102_; lean_object* v_res_103_; 
v_contentHash_boxed_102_ = lean_unbox_uint64(v_contentHash_100_);
lean_dec_ref(v_contentHash_100_);
v_res_103_ = l_Lake_artifactWithExt(v_contentHash_boxed_102_, v_ext_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_relPath(lean_object* v_self_104_){
_start:
{
uint64_t v_hash_105_; lean_object* v_ext_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_hash_105_ = lean_ctor_get_uint64(v_self_104_, sizeof(void*)*1);
v_ext_106_ = lean_ctor_get(v_self_104_, 0);
v___x_107_ = lean_string_utf8_byte_size(v_ext_106_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_nat_dec_eq(v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_110_ = l_Lake_lowerHexUInt64(v_hash_105_);
v___x_111_ = ((lean_object*)(l_Lake_artifactPath___closed__0));
v___x_112_ = lean_string_append(v___x_110_, v___x_111_);
v___x_113_ = lean_string_append(v___x_112_, v_ext_106_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = l_Lake_lowerHexUInt64(v_hash_105_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_relPath___boxed(lean_object* v_self_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lake_ArtifactDescr_relPath(v_self_115_);
lean_dec_ref(v_self_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToString___lam__0(lean_object* v_x_117_){
_start:
{
uint64_t v_hash_118_; lean_object* v_ext_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_hash_118_ = lean_ctor_get_uint64(v_x_117_, sizeof(void*)*1);
v_ext_119_ = lean_ctor_get(v_x_117_, 0);
v___x_120_ = lean_string_utf8_byte_size(v_ext_119_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = l_Lake_lowerHexUInt64(v_hash_118_);
v___x_124_ = ((lean_object*)(l_Lake_artifactPath___closed__0));
v___x_125_ = lean_string_append(v___x_123_, v___x_124_);
v___x_126_ = lean_string_append(v___x_125_, v_ext_119_);
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = l_Lake_lowerHexUInt64(v_hash_118_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToString___lam__0___boxed(lean_object* v_x_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lake_ArtifactDescr_instToString___lam__0(v_x_128_);
lean_dec_ref(v_x_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToJson___lam__0(lean_object* v_x_132_){
_start:
{
uint64_t v_hash_133_; lean_object* v_ext_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_hash_133_ = lean_ctor_get_uint64(v_x_132_, sizeof(void*)*1);
v_ext_134_ = lean_ctor_get(v_x_132_, 0);
v___x_135_ = lean_string_utf8_byte_size(v_ext_134_);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_nat_dec_eq(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_138_ = l_Lake_lowerHexUInt64(v_hash_133_);
v___x_139_ = ((lean_object*)(l_Lake_artifactPath___closed__0));
v___x_140_ = lean_string_append(v___x_138_, v___x_139_);
v___x_141_ = lean_string_append(v___x_140_, v_ext_134_);
v___x_142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l_Lake_lowerHexUInt64(v_hash_133_);
v___x_144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToJson___lam__0___boxed(lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lake_ArtifactDescr_instToJson___lam__0(v_x_145_);
lean_dec_ref(v_x_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(lean_object* v___x_149_, lean_object* v_s_150_, lean_object* v_a_151_, lean_object* v_b_152_){
_start:
{
uint8_t v_decide_153_; 
v_decide_153_ = lean_nat_dec_eq(v_a_151_, v___x_149_);
if (v_decide_153_ == 0)
{
uint32_t v___x_154_; uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_154_ = lean_string_utf8_get_fast(v_s_150_, v_a_151_);
v___x_155_ = 46;
v___x_156_ = lean_uint32_dec_eq(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_box(0);
v___x_158_ = lean_string_utf8_next_fast(v_s_150_, v_a_151_);
lean_dec(v_a_151_);
v_a_151_ = v___x_158_;
v_b_152_ = v___x_157_;
goto _start;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v_a_151_);
return v___x_160_;
}
}
else
{
lean_dec(v_a_151_);
lean_inc(v_b_152_);
return v_b_152_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg___boxed(lean_object* v___x_161_, lean_object* v_s_162_, lean_object* v_a_163_, lean_object* v_b_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(v___x_161_, v_s_162_, v_a_163_, v_b_164_);
lean_dec(v_b_164_);
lean_dec_ref(v_s_162_);
lean_dec(v___x_161_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f(lean_object* v_path_170_){
_start:
{
lean_object* v___y_172_; lean_object* v_searcher_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_searcher_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_string_utf8_byte_size(v_path_170_);
v___x_206_ = lean_box(0);
v___x_207_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(v___x_205_, v_path_170_, v_searcher_204_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
v___y_172_ = v___x_205_;
goto v___jp_171_;
}
else
{
lean_object* v_val_208_; 
v_val_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_207_, 1);
v___y_172_ = v_val_208_;
goto v___jp_171_;
}
v___jp_171_:
{
lean_object* v___x_173_; uint8_t v_decide_174_; 
v___x_173_ = lean_string_utf8_byte_size(v_path_170_);
v_decide_174_ = lean_nat_dec_eq(v___y_172_, v___x_173_);
if (v_decide_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_string_utf8_extract_fast(v_path_170_, v___x_175_, v___y_172_);
v___x_177_ = l_Lake_Hash_ofHex_x3f(v___x_176_);
lean_dec_ref(v___x_176_);
if (lean_obj_tag(v___x_177_) == 1)
{
lean_object* v_val_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_189_; 
v_val_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_189_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_189_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_val_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_189_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v_ext_183_; lean_object* v___x_184_; uint64_t v___x_185_; lean_object* v___x_187_; 
v___x_182_ = lean_string_utf8_next_fast(v_path_170_, v___y_172_);
lean_dec(v___y_172_);
v_ext_183_ = lean_string_utf8_extract_fast(v_path_170_, v___x_182_, v___x_173_);
v___x_184_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_184_, 0, v_ext_183_);
v___x_185_ = lean_unbox_uint64(v_val_178_);
lean_dec(v_val_178_);
lean_ctor_set_uint64(v___x_184_, sizeof(void*)*1, v___x_185_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_184_);
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_184_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
else
{
lean_object* v___x_190_; 
lean_dec(v___x_177_);
lean_dec(v___y_172_);
v___x_190_ = ((lean_object*)(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1));
return v___x_190_;
}
}
else
{
lean_object* v___x_191_; 
lean_dec(v___y_172_);
v___x_191_ = l_Lake_Hash_ofHex_x3f(v_path_170_);
if (lean_obj_tag(v___x_191_) == 1)
{
lean_object* v_val_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_202_; 
v_val_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_202_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_202_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_val_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_202_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; uint64_t v___x_198_; lean_object* v___x_200_; 
v___x_196_ = ((lean_object*)(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2));
v___x_197_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_197_, 0, v___x_196_);
v___x_198_ = lean_unbox_uint64(v_val_192_);
lean_dec(v_val_192_);
lean_ctor_set_uint64(v___x_197_, sizeof(void*)*1, v___x_198_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_197_);
v___x_200_ = v___x_194_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_197_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
else
{
lean_object* v___x_203_; 
lean_dec(v___x_191_);
v___x_203_ = ((lean_object*)(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1));
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f___boxed(lean_object* v_path_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_path_209_);
lean_dec_ref(v_path_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0(lean_object* v___x_211_, lean_object* v___x_212_, lean_object* v_s_213_, lean_object* v_inst_214_, lean_object* v_R_215_, lean_object* v_a_216_, lean_object* v_b_217_, lean_object* v_c_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(v___x_211_, v_s_213_, v_a_216_, v_b_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___boxed(lean_object* v___x_220_, lean_object* v___x_221_, lean_object* v_s_222_, lean_object* v_inst_223_, lean_object* v_R_224_, lean_object* v_a_225_, lean_object* v_b_226_, lean_object* v_c_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0(v___x_220_, v___x_221_, v_s_222_, v_inst_223_, v_R_224_, v_a_225_, v_b_226_, v_c_227_);
lean_dec(v_b_226_);
lean_dec_ref(v_s_222_);
lean_dec_ref(v___x_221_);
lean_dec(v___x_220_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object* v_data_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Json_getStr_x3f(v_data_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_241_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_241_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_236_ = ((lean_object*)(l_Lake_ArtifactDescr_fromJson_x3f___closed__0));
v___x_237_ = lean_string_append(v___x_236_, v_a_232_);
lean_dec(v_a_232_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_237_);
v___x_239_ = v___x_234_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_243_; 
v_a_242_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v___x_231_, 1);
v___x_243_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_a_242_);
lean_dec(v_a_242_);
return v___x_243_;
}
}
}
static lean_object* _init_l_Lake_instInhabitedArtifact_default___closed__0(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_nat_to_int(v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifact_default___closed__1(void){
_start:
{
uint32_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = 0;
v___x_249_ = lean_obj_once(&l_Lake_instInhabitedArtifact_default___closed__0, &l_Lake_instInhabitedArtifact_default___closed__0_once, _init_l_Lake_instInhabitedArtifact_default___closed__0);
v___x_250_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set_uint32(v___x_250_, sizeof(void*)*1, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifact_default___closed__2(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = lean_obj_once(&l_Lake_instInhabitedArtifact_default___closed__1, &l_Lake_instInhabitedArtifact_default___closed__1_once, _init_l_Lake_instInhabitedArtifact_default___closed__1);
v___x_252_ = ((lean_object*)(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2));
v___x_253_ = l_Lake_instInhabitedArtifactDescr_default;
v___x_254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
lean_ctor_set(v___x_254_, 2, v___x_252_);
lean_ctor_set(v___x_254_, 3, v___x_251_);
return v___x_254_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifact_default(void){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_obj_once(&l_Lake_instInhabitedArtifact_default___closed__2, &l_Lake_instInhabitedArtifact_default___closed__2_once, _init_l_Lake_instInhabitedArtifact_default___closed__2);
return v___x_255_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifact(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lake_instInhabitedArtifact_default;
return v___x_256_;
}
}
static lean_object* _init_l_Lake_instReprArtifact_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(9u);
v___x_267_ = lean_nat_to_int(v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr___redArg(lean_object* v_x_280_){
_start:
{
lean_object* v_descr_281_; lean_object* v_path_282_; lean_object* v_name_283_; lean_object* v_mtime_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_descr_281_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_descr_281_);
v_path_282_ = lean_ctor_get(v_x_280_, 1);
lean_inc_ref(v_path_282_);
v_name_283_ = lean_ctor_get(v_x_280_, 2);
lean_inc_ref(v_name_283_);
v_mtime_284_ = lean_ctor_get(v_x_280_, 3);
lean_inc_ref(v_mtime_284_);
lean_dec_ref(v_x_280_);
v___x_285_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__5));
v___x_286_ = ((lean_object*)(l_Lake_instReprArtifact_repr___redArg___closed__3));
v___x_287_ = lean_obj_once(&l_Lake_instReprArtifact_repr___redArg___closed__4, &l_Lake_instReprArtifact_repr___redArg___closed__4_once, _init_l_Lake_instReprArtifact_repr___redArg___closed__4);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Lake_instReprArtifactDescr_repr___redArg(v_descr_281_);
v___x_290_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_287_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = 0;
v___x_292_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1, v___x_291_);
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_286_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__9));
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_box(1);
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = ((lean_object*)(l_Lake_instReprArtifact_repr___redArg___closed__6));
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_285_);
v___x_301_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__7, &l_Lake_instReprArtifactDescr_repr___redArg___closed__7_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__7);
v___x_302_ = ((lean_object*)(l_Lake_instReprArtifact_repr___redArg___closed__8));
v___x_303_ = l_String_quote(v_path_282_);
v___x_304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_302_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Repr_addAppParen(v___x_305_, v___x_288_);
v___x_307_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_301_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*1, v___x_291_);
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_300_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_294_);
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_296_);
v___x_312_ = ((lean_object*)(l_Lake_instReprArtifact_repr___redArg___closed__10));
v___x_313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_285_);
v___x_315_ = l_String_quote(v_name_283_);
v___x_316_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
v___x_317_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_301_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*1, v___x_291_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_314_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_294_);
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_296_);
v___x_322_ = ((lean_object*)(l_Lake_instReprArtifact_repr___redArg___closed__12));
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_285_);
v___x_325_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_284_);
lean_dec_ref(v_mtime_284_);
v___x_326_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_287_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v___x_291_);
v___x_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_324_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__15, &l_Lake_instReprArtifactDescr_repr___redArg___closed__15_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__15);
v___x_330_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__16));
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_328_);
v___x_332_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__17));
v___x_333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_329_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*1, v___x_291_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr(lean_object* v_x_336_, lean_object* v_prec_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lake_instReprArtifact_repr___redArg(v_x_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr___boxed(lean_object* v_x_339_, lean_object* v_prec_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lake_instReprArtifact_repr(v_x_339_, v_prec_340_);
lean_dec(v_prec_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_Artifact_withName(lean_object* v_name_344_, lean_object* v_self_345_){
_start:
{
lean_object* v_descr_346_; lean_object* v_path_347_; lean_object* v_mtime_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
v_descr_346_ = lean_ctor_get(v_self_345_, 0);
v_path_347_ = lean_ctor_get(v_self_345_, 1);
v_mtime_348_ = lean_ctor_get(v_self_345_, 3);
v_isSharedCheck_355_ = !lean_is_exclusive(v_self_345_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; 
v_unused_356_ = lean_ctor_get(v_self_345_, 2);
lean_dec(v_unused_356_);
v___x_350_ = v_self_345_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_mtime_348_);
lean_inc(v_path_347_);
lean_inc(v_descr_346_);
lean_dec(v_self_345_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 2, v_name_344_);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_descr_346_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_path_347_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_name_344_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_mtime_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Artifact_useLocalFile(lean_object* v_path_357_, lean_object* v_self_358_){
_start:
{
lean_object* v_descr_359_; lean_object* v_mtime_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_descr_359_ = lean_ctor_get(v_self_358_, 0);
v_mtime_360_ = lean_ctor_get(v_self_358_, 3);
v_isSharedCheck_367_ = !lean_is_exclusive(v_self_358_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; lean_object* v_unused_369_; 
v_unused_368_ = lean_ctor_get(v_self_358_, 2);
lean_dec(v_unused_368_);
v_unused_369_ = lean_ctor_get(v_self_358_, 1);
lean_dec(v_unused_369_);
v___x_362_ = v_self_358_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_mtime_360_);
lean_inc(v_descr_359_);
lean_dec(v_self_358_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
lean_inc_ref(v_path_357_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 2, v_path_357_);
lean_ctor_set(v___x_362_, 1, v_path_357_);
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_descr_359_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_path_357_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_path_357_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_mtime_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Artifact_trace(lean_object* v_self_372_){
_start:
{
lean_object* v_descr_373_; lean_object* v_name_374_; lean_object* v_mtime_375_; uint64_t v_hash_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_descr_373_ = lean_ctor_get(v_self_372_, 0);
v_name_374_ = lean_ctor_get(v_self_372_, 2);
v_mtime_375_ = lean_ctor_get(v_self_372_, 3);
v_hash_376_ = lean_ctor_get_uint64(v_descr_373_, sizeof(void*)*1);
v___x_377_ = ((lean_object*)(l_Lake_Artifact_trace___closed__0));
lean_inc_ref(v_mtime_375_);
lean_inc_ref(v_name_374_);
v___x_378_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_378_, 0, v_name_374_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
lean_ctor_set(v___x_378_, 2, v_mtime_375_);
lean_ctor_set_uint64(v___x_378_, sizeof(void*)*3, v_hash_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Artifact_trace___boxed(lean_object* v_self_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lake_Artifact_trace(v_self_379_);
lean_dec_ref(v_self_379_);
return v_res_380_;
}
}
lean_object* runtime_initialize_Lake_Build_Trace(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Artifact(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Build_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedArtifactDescr_default = _init_l_Lake_instInhabitedArtifactDescr_default();
lean_mark_persistent(l_Lake_instInhabitedArtifactDescr_default);
l_Lake_instInhabitedArtifactDescr = _init_l_Lake_instInhabitedArtifactDescr();
lean_mark_persistent(l_Lake_instInhabitedArtifactDescr);
l_Lake_instInhabitedArtifact_default = _init_l_Lake_instInhabitedArtifact_default();
lean_mark_persistent(l_Lake_instInhabitedArtifact_default);
l_Lake_instInhabitedArtifact = _init_l_Lake_instInhabitedArtifact();
lean_mark_persistent(l_Lake_instInhabitedArtifact);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Artifact(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Trace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Artifact(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Artifact(builtin);
}
#ifdef __cplusplus
}
#endif
