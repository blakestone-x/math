"""Check the claimed prefix by enumerating and sorting actual partitions."""


def partitions(total):
    if total == 0:
        return [()]
    return sorted(((part,) + tail
                   for part in range(1, total + 1)
                   for tail in rows[total - part]
                   if not tail or part >= tail[0]), reverse=True)


rows = []
for size in range(27):
    rows.append(partitions(size))
limit = [1 + len(tail) for row in rows for tail in row]
for n in range(1, 27):
    row = [len(partition) for partition in rows[n]]
    actual = next((j for j, (x, y) in enumerate(zip(row, limit)) if x != y),
                  len(row))
    palindromic = sum(sum(partition.count(x) % 2 for x in set(partition)) <= 1
                      for partition in rows[n])
    assert actual == palindromic == sum(len(block) for block in rows[:n//2 + 1])
print("Exact prefix length and palindromic-partition count agree for n=1..26.")
