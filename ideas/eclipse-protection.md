- Research possible radio spectrum options (bandwidth, error correction, range)
- Research required radio licensing
- Research satellite options (Iridium definitely possible)
- Research notarization options (into other PoW/PoS chains)

Latest Notes: 
- Promise that we build and release guide on how to set it up. It becomes problematic, licenses requirements, for using it. 
- Legality: Broadcasting within Switzerland would not be an issue as long as it's offered by a non-profit organisation, e.g. Tezos Switzerland, Cryptovalley Association. As long as it is amateur, and not in interference with anything else. Being able to broadcast within Europe will already be significant. 
- Development

TODO:
- Further feasibility research
- Explore into what long-range IoT companies do
- Legality
- [ ] Write-up a document with the initial idea and main challenges
  * What's the purpose? Censorship resistance, bakers getting out of sync and dos resistance, light-clients
  * What are the possible implementations?
- Meeting with Ryan (FOAM)

Technically this is feasible.

The main headache for radio will be to get the licenses.

[nationaler_frequenzzuweisungsplan2018.pdf](https://github.com/cryptiumlabs/company/files/2396925/nationaler_frequenzzuweisungsplan2018.pdf)

Possible resource: existing long-range IoT solutions
- https://www.sigfox.com/en/coverage
- https://www.electronicdesign.com/industrial-automation/choices-abound-long-range-wireless-iot

Relevant software reference - https://github.com/brannondorsey/chattervox
Meshnet approach - https://www.sparkfun.com/products/14984

Another Iridium option - [Iridium Go](https://www.predictwind.com/iridium-go/?satellite). Unlimited data plan is $140/month, which is not that ridiculous (especially compared to the [per-message costs for the smaller unit](https://docs.rockblock.rock7.com/docs/iridium-contract-costs)).

[This review](https://www.macworld.com/article/3048163/hardware/iridium-go-satellite-hotspot-review-more-like-iridium-no.html) wasn't too positive, but we may have less stringent requirements. [This review](https://ausdroid.net/2017/05/10/wild-iridium-go/) thought the internet worked OK, albeit slowly (but syncing block headers shouldn't require much).
