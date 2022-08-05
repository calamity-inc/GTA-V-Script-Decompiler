#include <cstdint>
#include <string>
#include <fstream>
#include <iostream>
#include <unordered_set>

char to_lower(const char c)
{
	return (c >= 'A' && c <= 'Z') ? c + ('a' - 'A') : c;
}

std::uint32_t joaat(const std::string& str)
{
	std::uint32_t hash = 0;
	for (const char c : str)
	{
		hash += to_lower(c);
		hash += (hash << 10);
		hash ^= (hash >> 6);
	}
	hash += (hash << 3);
	hash ^= (hash >> 11);
	hash += (hash << 15);
	return hash;
}

int main()
{
	std::ofstream os("Entities.txt");
	constexpr const char* in_files[] = {
		"Entities_gta-v-joaat-hash-db.txt",
		"Entities_tunables.txt",
		"Entities_dumpster_reduced.txt",
	};
	std::unordered_set<std::int32_t> included_hashes = {};
	for(const auto& in_file : in_files)
	{
		std::ifstream is(in_file);
		std::string line;
		while(std::getline(is, line))
		{
			if(line.empty())
			{
				continue;
			}
			const auto hash = (std::int32_t)joaat(line);
			if(included_hashes.find(hash) != included_hashes.end())
			{
				continue;
			}
			os << std::to_string(hash) << ":" << line << "\n";
			included_hashes.emplace(hash);
		}
	}
	return 0;
}
