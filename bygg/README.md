# Sidbyggaren

Kopierad från fis-detektor av `tools/publicera_bygg.py`. Ändra där, inte här.
GitHub Actions (`.github/workflows/bygg.yml`) kör `fisrapport.py --offline`
varje timme: nya fisar från fisdatabasen läggs i `arkiv.json`, och
`index.html` byggs om.
