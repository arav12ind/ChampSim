#include <bitset>
#include <cstdint>
#include <iostream>
#include <boost/circular_buffer.hpp>
#include <boost/circular_buffer/base.hpp>
#include <list>
#include <map>
#include <math.h>
#include <stdexcept>
#include <vector>

#include "ooo_cpu.h"


using std::string;
using std::invalid_argument;
using std::bitset;
using std::cout;
using std::cin;
using std::hex;
using std::dec;


template<uint n>
class circular_buffer
{
    uint64_t buf[n];
    uint tail;
    bool full;
    public:
    circular_buffer<n>()
    {
        tail=0;
        full=false;
    }
    int size()
    {
        return full?n:tail;
    }
    uint get_tail()
    {
        return tail;
    }
    bool is_full()
    {
        return full;
    }
    uint64_t &operator[](int i)
    {
        return buf[i];
    }
    void push_back(uint64_t x)
    {
        buf[tail++]=x;
        tail=tail==n?0:tail;
    }
};

circular_buffer<1024> imiss_log;
int prefetch_depth=3;


class idx_entry
{
    public:
    uint64_t tag;
    uint idx;
    bool valid;
    idx_entry(uint64_t tag=0,uint idx=0,bool valid=false)
    {
        this->tag=tag;
        this->idx=idx;
        this->valid=valid;
    }
    idx_entry(const idx_entry &x)
    {
      set(x);
    }
    void set(const idx_entry &x)
    {
      this->tag=x.tag;
      this->idx=x.idx;
      this->valid=x.valid;
    }
    bool operator==(const idx_entry &b1)
    {
        return this->tag==b1.tag;
    }
    friend std::ostream& operator<<(std::ostream& os, const idx_entry &p)
    {
      os<<"("<<hex<<p.tag<<dec<<","<<p.idx<<","<<p.valid<<")";
      return os;
    }
};

class idx_set
{
    protected:
    /**
    * @param ways is the number of lines in the set.
    */
    const uint ways;

    public:
    
    idx_set(const uint ways) :ways(ways)
    {}

    //* Method for simulating memory access in a cache set.
    virtual bool get(idx_entry &ent)=0;

};


/*****************************************************************************************************************************/
class lru_idx_set : public idx_set
{
    /**
    * * A queue of all the valid lines in the set, so no need for valid bit in idx_entry.
    */
    std::list<idx_entry> idx_entries;
    
    public:
    static const string replacement_algo;
    //* No specific initialization needed, so call only the base class constructor.
    lru_idx_set(uint ways) : idx_set(ways)
    {}

    /**
    * * Implements memory access with FIFO replacement algorithm.
    * * Returns if it was a hit or not.
    * TODO: Sperate out reads and writes
    * TODO: Count the number of modified lines replaced.
    */


    virtual bool get(idx_entry &ent) override
    {
        //* Check if the line is in the set.
        idx_entry t=ent;
        // cout<<"\nElements : ";
        // for(auto ii=idx_entries.begin();ii!=idx_entries.end();++ii)
        // {
        //     cout<<*ii<<"\t";
        // }
        // cout<<"\n";
        auto it = find(idx_entries.begin(),idx_entries.end(),t);

        #ifdef DEBUG
            cout<<"Tag  : "<<hex<<cch_line.tag<<dec<<"\tHit : "<<(it!=idx_entries.end()?"True":"False")<<endl;
        #endif

        //* If the line is not present in the set.
        // cout<<"Find : "<<it->tag<<"\n";
        if(it==idx_entries.end() and it->tag!=t.tag)
        {
            //* Re-use the node that is being replaced.
            if(idx_entries.size()==ways)
            {
                idx_entries.splice(idx_entries.end(),idx_entries,idx_entries.begin());
                std::prev(idx_entries.end())->set(t);
            }
            //* No need for replacement, just push the line to the queue.
            else
            {
                idx_entries.push_back(t);
            }
            return false;
        }
        //* Put the used line at the end of the queue
        else
        {
          ent=*it;
          idx_entries.splice(idx_entries.end(),idx_entries,it);
          std::prev(idx_entries.end())->set(t);
          return true;
        }
    }
    //* Prints the tag of lines in the set.
    void print()
    {
        cout<<"lines : ";
        for(const auto &i:idx_entries)
            cout<<i<<" || ";
        cout<<"\n";
    }
};
const string lru_idx_set::replacement_algo = "LRU";

//boost::circular_buffer<uint64_t> imiss_log(1024);

//* Seperated from the cache class for making a vector of caches.
template<class idx_set>
class IndexTable
{
    /**
    * @param ways is the set associativity of the cache.
    * @param no_of_sets is the number of sets in the cache.
    * @param set_bits no. of bits required for indexing sets.
    * @param tag_bits no. of bits required for tag.
    * @param set_mask for getting only the index portion of the address.
    * @param tag_mask for getting only the tag portion of the address.
    * @param addr_bits address length.
    */
    protected:
    const string name,replacement_algo;
    const uint ways,no_of_sets,blk_size;
    uint byte_bits,set_bits,tag_bits;
    std::vector<idx_set> sets;
    uint64_t byte_mask,set_mask,tag_mask;
    const uint addr_bits=64;
    public:
    IndexTable(const string &name,const string &replacement_algo,const uint no_of_sets,const uint ways,const uint blk_size) : 
    name(name),replacement_algo(replacement_algo),ways(ways),no_of_sets(no_of_sets),blk_size(blk_size)
    {
        if(no_of_sets==0)
            throw invalid_argument("no_of_sets should be a positive integer");
        if(ways==0)
            throw invalid_argument("Ways should be a positive integer");
        byte_bits= log2(blk_size);
        set_bits = log2(no_of_sets);
        tag_bits = addr_bits-set_bits-byte_bits;
        if(byte_bits<addr_bits)
            byte_mask=((1<<byte_bits)-1);
        else
         byte_mask=-1;
        if(set_bits<addr_bits)
            set_mask=((1<<set_bits)-1)<<byte_bits;
        else
            set_mask=-1;
        if(tag_bits<addr_bits)
            tag_mask=((1<<tag_bits)-1)<<(byte_bits+set_bits);
        else
            tag_mask=-1;
        for(uint i=0;i<no_of_sets;++i)
        {
            idx_set N(ways);
            sets.push_back(N);
        }
    }
    
    //* Overloading << operator for output.
    friend std::ostream& operator<<(std::ostream& os, const IndexTable &p)
    {
        return os
            <<"\nCache Name             = "<<p.name
            <<"\nReplacement Algorithm  = "<<p.replacement_algo
            <<"\nWays                   = "<<p.ways
            <<"\nNo of sets             = "<<p.no_of_sets
            <<"\nbyte_bits              = "<<p.byte_bits
            <<"\nset_bits               = "<<p.set_bits
            <<"\ntag_bits               = "<<p.tag_bits
            <<"\nbyte_mask              = "<<bitset<8*sizeof(uint64_t)>(p. byte_mask)
            <<"\nset_mask               = "<<bitset<8*sizeof(uint64_t)>(p.set_mask)
            <<"\ntag_mask               = "<<bitset<8*sizeof(uint64_t)>(p.tag_mask);
    }
    uint64_t get_blk_addr(uint64_t addr)
    {
        return addr&(tag_mask+set_mask);
    }
    idx_entry get(uint64_t blk_addr,uint tail)
    {
      uint64_t set_no= (set_mask&blk_addr)>>byte_bits;
      //cout<<"\nSet no : "<<set_no<<"  Blk_addr : "<<blk_addr;
      uint64_t tag   = tag_mask&blk_addr;
      idx_entry idx(tag,tail,true);
      bool found=sets[set_no].get(idx);
      if(found)
      {
        if(imiss_log[idx.idx]==blk_addr)
        {
          return idx_entry(tag,idx.idx,true);
        }
      }
      return idx_entry(tag,idx.idx,false);
    }
};

IndexTable<lru_idx_set> idx_table("Index Table","LRU",1024,4,64);

void O3_CPU::prefetcher_initialize()
{ 
  cout << "CPU " << cpu << " TIFS prefetcher"<< idx_table << endl;
}

void O3_CPU::prefetcher_branch_operate(uint64_t ip, uint8_t branch_type, uint64_t branch_target) {

}

uint32_t O3_CPU::prefetcher_cache_operate(uint64_t v_addr, uint8_t cache_hit, uint8_t prefetch_hit, uint32_t metadata_in)
{
  if(cache_hit==0)
  {
      uint64_t blk_addr=idx_table.get_blk_addr(v_addr);
      idx_entry idx_ent=idx_table.get(blk_addr,imiss_log.get_tail());
      imiss_log.push_back(blk_addr);
      if(idx_ent.valid)
      {
        auto size=imiss_log.size();
        for(int i=0;i<prefetch_depth and idx_ent.idx+i<size;++i)
        {
          prefetch_code_line(imiss_log[idx_ent.idx+i+1]);
        }
      }
  }
  return metadata_in;
}

void O3_CPU::prefetcher_cycle_operate() {}

uint32_t O3_CPU::prefetcher_cache_fill(uint64_t v_addr, uint32_t set, uint32_t way, uint8_t prefetch, uint64_t evicted_v_addr, uint32_t metadata_in)
{
  return metadata_in;
}

void O3_CPU::l1i_prefetcher_final_stats() {}
