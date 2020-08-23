#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iostream>
#include <streambuf>
#include <string>
#include <sstream>
#include <utility>

typedef uint32_t u32;
typedef uint16_t u16;
typedef uint8_t u8;

namespace Lz4pj {

  const u32 MIN_MATCH_OFFSET = 1;
  
  const u32 NO_MAX_MATCH_LEN = 0;
  const u32 NO_MAX_MATCH_OFFSET = 0;
  
  const u32 MIN_MAIN_PASS_MATCH_LEN = 4;
  const u32 MAX_MAIN_PASS_MATCH_LEN = NO_MAX_MATCH_LEN;
  const u32 MAX_MAIN_PASS_MATCH_OFFSET = NO_MAX_MATCH_OFFSET;

  const u32 MIN_3BYTE_PASS_MATCH_LEN = 3;
  const u32 MAX_3BYTE_PASS_MATCH_LEN = 3;
  const u32 MAX_3BYTE_PASS_MATCH_OFFSET = 256;
  
  const u32 MIN_2BYTE_PASS_MATCH_LEN = 2;
  const u32 MAX_2BYTE_PASS_MATCH_LEN = 2;
  const u32 MAX_2BYTE_PASS_MATCH_OFFSET = 256;
  
  template <u32 MAX_MATCH_OFFSET>
  struct out_buf {
    u8* buf;
    u32 index;
    
    out_buf(u8* buf, u32 index): buf(buf), index(0) {}
    
    void out(u8 byte) {
      buf[index++] = byte;
    }
    
    void write_bytes(u8* bytes, u32 n_bytes) {
      memcpy(&buf[index], bytes, (size_t)n_bytes);
      index += n_bytes;
    }
    
    void write_utf8_len(u32 len) {
      if(len == 0) {
	out(0);
      }
      while(len) {
	u8 hibit = len < 128 ? 0 : 0x80;
	out((u8)(len & 0x7f) | hibit);
	len = len >> 7;
      }
    }
    
    void write_long_len(u32 len) {
      if(len >= 15) {
	len -= 15;
	
	if(len < 255) {
	  out(len);
	} else {
	  out(255);
	  len -= 255;
	  if(len < 255 * 256) {
	    out((u8)(len >> 8));
	    out((u8)len);
	  } else {
	    out(255);
	    out((u8)(len >> 24));
	    out((u8)(len >> 16));
	    out((u8)(len >> 8));
	    out((u8)len);
	  }
	}
      }
    }
    
    void write_len_pair(u32 len1, u32 len2, u32 min_len) {
      len1 -= min_len;
      u8 nibble1 = len1 < 15 ? len1 : 15;
      len2 -= min_len;
      u8 nibble2 = len2 < 15 ? len2 : 15;
      
      u8 nibble_pair = (nibble1 << 4) | nibble2;
      out(nibble_pair);
      
      write_long_len(len1);
      write_long_len(len2);
    }
    
    void write_lens(u32* lens, u32 n_lens, u32 min_len) {
      for(u32 i = 0; i < n_lens-1; i += 2) {
	write_len_pair(lens[i], lens[i+1], min_len);
      }
      if(n_lens & 1) {
	write_len_pair(lens[n_lens-1], 0, min_len);
      }
    }
    
    void write_match_offset(u32 offset) {
      if(MAX_MATCH_OFFSET - MIN_MATCH_OFFSET < 256) {
	out((u8)offset);
      } else {
	write_utf8_len(offset - MIN_MATCH_OFFSET);
      }
    }
    
    void write_match_offsets(u32* offsets, u32 n_offsets) {
      for(u32 i = 0; i < n_offsets; i++) {
	write_match_offset(offsets[i]);
      }
    }
  };

  template <u32 MIN_MATCH_LEN, u32 MAX_MATCH_LEN, u32 MAX_MATCH_OFFSET>
  struct Lz4pjCState {
    static const u8 VERSION = 0;
    
    u32* last_bytepair_indexes;

    u32* lit_lens;
    u32* match_lens;
    u32* match_offsets;
    u32 n_chunks;

    u32 trailing_lit_len;

    u8* lits;
    u32 n_lits;

    Lz4pjCState() {
      last_bytepair_indexes = new u32[256*256];
    }

    ~Lz4pjCState() {
      delete[] last_bytepair_indexes;
    }

    void init(size_t raw_len) {
      // Each match is at least 4 bytes
      const size_t max_nchunks = (raw_len + 3)/4;
      
      lit_lens = new u32[max_nchunks];
      match_lens = new u32[max_nchunks];
      match_offsets = new u32[max_nchunks];
      n_chunks = 0;

      lits = new u8[raw_len];
      n_lits = 0;

      trailing_lit_len = 0;
    }

    void cleanup() {
      delete[] lit_lens;
      delete[] match_lens;
      delete[] match_offsets;

      delete[] lits;
    }

    static u16 get_byte_pair(const u8* raw, u32 index) {
      return (raw[index] << 8) | raw[index + 1];
    }
    
    static u32 get_match_len(const u8* raw, size_t raw_len, u32 index, u32 match_index) {
      // Handle unitialised match-index array
      if(index <= match_index) { return 0; }
      
      u32 start_index = index;
      while(index < raw_len && (MAX_MATCH_LEN == NO_MAX_MATCH_LEN || index < start_index + MAX_MATCH_LEN) && raw[index] == raw[match_index]) {
	index++; match_index++;
      }
      return index - start_index;
    }

    void add_chunk(u32 lit_len, u32 match_len, u32 match_offset) {
      lit_lens[n_chunks] = lit_len;
      match_lens[n_chunks] = match_len;
      match_offsets[n_chunks] = match_offset;

      n_chunks++;
    }

    void generate_chunks(const void* raw_void, const u32 raw_len) {
      const u8* raw = (const u8*) raw_void;
      
      if(raw_len == 0) {
	return;
      }

      u32 start_lit_index = 0;
      for(u32 index = 0; index < raw_len - 1; ) {
	const u16 byte_pair = get_byte_pair(raw, index);

	// Get the last byte-pair match
	const u32 match_index = last_bytepair_indexes[byte_pair];
	// ... and update it
	last_bytepair_indexes[byte_pair] = index;

	u32 match_len = get_match_len(raw, raw_len, index, match_index);

	//printf("                      index %u byte-pair 0x%4x match-index %u match-len %u\n", index, byte_pair, match_index, match_len);

	if(match_len >= MIN_MATCH_LEN) {
	  u32 lit_len = index - start_lit_index;
	  u32 match_offset = index - match_index;
	  add_chunk(lit_len, match_len, match_offset);

	  // skip the match but update byte-pair indexes
	  start_lit_index = std::min<u32>(index + match_len, raw_len - 1);
	  index++; 
	  while(index < start_lit_index) {
	    const u16 byte_pair = get_byte_pair(raw, index);
	    last_bytepair_indexes[byte_pair] = index;
	    index++;
	  }
	} else {
	  lits[n_lits++] = raw[index++];
	}
      }

      trailing_lit_len = raw_len - start_lit_index;
      if(trailing_lit_len) {
	// We miss the last byte cos we only look at byte-pairs in the main loop
	lits[n_lits++] = raw[raw_len - 1];
      }
    }

    // @return size

    u32 write_compressed(void* compressed_void, u32 compressed_len) {
      printf("%u chunks, %u lits, %u trailing-lits\n", n_chunks, n_lits, trailing_lit_len);

      out_buf<MAX_MATCH_OFFSET> out((u8*)compressed_void, compressed_len);

      // Header
      out.out(VERSION);

      // Lit bytes
      out.write_utf8_len(n_lits);
      out.write_bytes(lits, n_lits);

      printf("After lits - compressed len is %u\n", out.index);

      // Chunks
      out.write_utf8_len(n_chunks);

      out.write_lens(lit_lens, n_chunks, 0/*min lit-len*/);
      printf("After lit lens - compressed len is %u\n", out.index);
      if(MIN_MATCH_LEN != MAX_MATCH_LEN) {
	out.write_lens(match_lens, n_chunks, MIN_MATCH_LEN);
	printf("After match lens - compressed len is %u\n", out.index);
      }

      out.write_match_offsets(match_offsets, n_chunks);
      printf("After match offsets - compressed len is %u\n", out.index);

      // Trailing lits
      out.write_utf8_len(trailing_lit_len);
      
      return out.index;
    }

    // size_t compress(const void* raw, size_t raw_len, void* compressed, size_t compressed_len) {
    //   init(raw_len);

    //   generate_chunks(raw, (u32)raw_len);

    //   size_t len = (size_t) write_compressed(compressed, (u32)compressed_len);

    //   cleanup();

    //   return len;
    // }
  };

} // namespace Lz4pj

// @return 0 iff failed to compress, otherwise compressed len
size_t lz4pj_compress(const void* raw, size_t raw_len, void* compressed, size_t compressed_len) {
  Lz4pj::Lz4pjCState<Lz4pj::MIN_MAIN_PASS_MATCH_LEN, Lz4pj::MAX_MAIN_PASS_MATCH_LEN, Lz4pj::MAX_MAIN_PASS_MATCH_OFFSET> cstate_main;

  cstate_main.init(raw_len);
  cstate_main.generate_chunks(raw, (u32)raw_len);
  
  Lz4pj::Lz4pjCState<Lz4pj::MIN_3BYTE_PASS_MATCH_LEN, Lz4pj::MAX_3BYTE_PASS_MATCH_LEN, Lz4pj::MAX_3BYTE_PASS_MATCH_OFFSET> cstate_3byte;
  cstate_3byte.init(cstate_main.n_lits);
  cstate_3byte.generate_chunks(cstate_main.lits, cstate_main.n_lits);

  size_t len_3byte = (size_t) cstate_3byte.write_compressed(compressed, (u32)compressed_len);
  cstate_3byte.cleanup();
  printf("3byte compressed len %lu\n", len_3byte);
  
  Lz4pj::Lz4pjCState<Lz4pj::MIN_2BYTE_PASS_MATCH_LEN, Lz4pj::MAX_2BYTE_PASS_MATCH_LEN, Lz4pj::MAX_2BYTE_PASS_MATCH_OFFSET> cstate_2byte;
  cstate_2byte.init(cstate_main.n_lits*2);
  cstate_2byte.generate_chunks(cstate_main.lits, cstate_main.n_lits);

  size_t len_2byte = (size_t) cstate_2byte.write_compressed(compressed, (u32)compressed_len);
  cstate_2byte.cleanup();
  printf("2byte compressed len %lu\n", len_2byte);
  
  size_t len = (size_t) cstate_main.write_compressed(compressed, (u32)compressed_len);
  cstate_main.cleanup();

  return len;
}

static std::string slurp(const std::string& filepath) {
  std::ifstream t(filepath);
  std::string str;

  t.seekg(0, std::ios::end);   
  str.reserve(t.tellg());
  t.seekg(0, std::ios::beg);
  
  str.assign((std::istreambuf_iterator<char>(t)),
	     std::istreambuf_iterator<char>());

  return str;
}

int main(int argc, char* argv[]) {
  if(argc < 3) {
    fprintf(stderr, "%s <in-file> <out-file>\n", argv[0]);
    exit(1);
  }

  char* raw_file = argv[1];
  std::string raw_str = slurp(raw_file);

  const void* raw = raw_str.c_str();
  size_t raw_len = raw_str.length();

  typedef std::chrono::high_resolution_clock Time;
  typedef std::chrono::duration<double> dsec;
  
  auto t0 = Time::now();
  
  size_t compressed_len = 2*raw_len; // worst case
  u8* compressed = new u8[compressed_len];

  size_t len = lz4pj_compress(raw, raw_len, compressed, compressed_len);

  if(len == 0) {
    fprintf(stderr, "Error compressing\n");
    exit(1);
  }

  auto t1 = Time::now();
  dsec ds = t1 - t0;
  double secs = ds.count();

  char* compressed_file = argv[2];
  std::ofstream out_fs(compressed_file);
  out_fs << std::string((char*)compressed, len);
  out_fs.close();

  printf("Input %s %lu bytes -> output %s %lu bytes in %.3lf ms %.3lf MB/s\n", raw_file, raw_len, compressed_file, len, secs*1000, (double)raw_len/secs/(1024*1024));
  
  delete[] compressed;
}
